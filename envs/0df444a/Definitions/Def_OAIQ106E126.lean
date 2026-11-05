-- Prove2me | Definitions.Def_OAIQ106E126
-- name    : OAIQ106E126
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:04:23.884786+00:00
-- url     : https://prove2.me/theorems/0334691d-1113-485c-8d71-15aae76b0f90
-- title:
--   Definitions bundle OAIQ106E126 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 414 declarations of OpenAI's Lean: 414 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1971`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1972`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1973`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1976`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1977`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1978`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1979`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource198`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1980`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1981`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1982`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1983`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1984`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1985`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1986`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1987`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1988`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1989`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource199`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1990`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1991`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1992`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1993`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1994`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1995`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1996`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1997`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1998`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource1999`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource20`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2000`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2001`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2002`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2003`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2004`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2005`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2006`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2007`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedSource2008` and 374 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSources_Arithmetic0`, `MutuallyUnbiased_MixedSources_Arithmetic1`, `MutuallyUnbiased_MixedSources_Arithmetic12`, `MutuallyUnbiased_MixedSources_Arithmetic123`, `MutuallyUnbiased_MixedSources_Arithmetic124`, `MutuallyUnbiased_MixedSources_Arithmetic125`, `MutuallyUnbiased_MixedSources_Arithmetic126`, `MutuallyUnbiased_MixedSources_Arithmetic127`, `MutuallyUnbiased_MixedSources_Arithmetic128`, `MutuallyUnbiased_MixedSources_Arithmetic129`, `MutuallyUnbiased_MixedSources_Arithmetic13`, `MutuallyUnbiased_MixedSources_Arithmetic130`, `MutuallyUnbiased_MixedSources_Arithmetic131`, `MutuallyUnbiased_MixedSources_Arithmetic132`, `MutuallyUnbiased_MixedSources_Arithmetic133`, `MutuallyUnbiased_MixedSources_Arithmetic134`, `MutuallyUnbiased_MixedSources_Arithmetic135`, `MutuallyUnbiased_MixedSources_Arithmetic14`, `MutuallyUnbiased_MixedSources_Arithmetic15`, `MutuallyUnbiased_MixedSources_Arithmetic16`, `MutuallyUnbiased_MixedSources_Arithmetic17`, `MutuallyUnbiased_MixedSources_Arithmetic18`, `MutuallyUnbiased_MixedSources_Arithmetic19`, `MutuallyUnbiased_MixedSources_Arithmetic2`, `MutuallyUnbiased_MixedSources_Arithmetic20`, `MutuallyUnbiased_MixedSources_Arithmetic21`, `MutuallyUnbiased_MixedSources_Arithmetic22`, `MutuallyUnbiased_MixedSources_Arithmetic23`, `MutuallyUnbiased_MixedSources_Arithmetic24`, `MutuallyUnbiased_MixedSources_Arithmetic4`.
--
--   **Imports.** It imports the bundles `OAIQ106E043` and `OAIQ106E084` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2074_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E084

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource2 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3801 x + ((4 : ℝ) * Sparse.eval nodeValue3809 x + ((4 : ℝ) * Sparse.eval nodeValue3853 x + ((2 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3910 x + ((2 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue4016 x + ((2 : ℝ) * Sparse.eval nodeValue4039 x + ((2 : ℝ) * Sparse.eval nodeValue4040 x + 0)))))))))))))

noncomputable def reducedSource3 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5301 x + ((4 : ℝ) * Sparse.eval nodeValue5302 x + ((2 : ℝ) * Sparse.eval nodeValue5306 x + ((4 : ℝ) * Sparse.eval nodeValue5412 x + ((2 : ℝ) * Sparse.eval nodeValue5437 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5453 x + ((4 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5456 x + 0))))))))

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

noncomputable def reducedSource20 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((2 : ℝ) * Sparse.eval nodeValue5481 x + ((1 : ℝ) * Sparse.eval nodeValue5484 x + ((2 : ℝ) * Sparse.eval nodeValue5489 x + ((3 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))))))))))

noncomputable def reducedSource21 (x : Master → ℝ) : ℝ :=
  (6 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((2 : ℝ) * Sparse.eval nodeValue5310 x + ((6 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5455 x + ((6 : ℝ) * Sparse.eval nodeValue5484 x + ((6 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))

noncomputable def reducedSource22 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4096 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((4 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5491 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5501 x + 0)))))))))))))

noncomputable def reducedSource23 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((2 : ℝ) * Sparse.eval nodeValue5454 x + ((4 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5489 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5492 x + ((2 : ℝ) * Sparse.eval nodeValue5493 x + ((2 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))))))))

noncomputable def reducedSource24 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((3 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((2 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5495 x + 0)))))))))))))))))))

noncomputable def reducedSource25 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((6 : ℝ) * Sparse.eval nodeValue4091 x + ((6 : ℝ) * Sparse.eval nodeValue4092 x + ((6 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue4094 x + ((3 : ℝ) * Sparse.eval nodeValue4096 x + ((2 : ℝ) * Sparse.eval nodeValue4097 x + 0)))))))

noncomputable def reducedSource26 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5452 x + ((8 : ℝ) * Sparse.eval nodeValue5482 x + ((4 : ℝ) * Sparse.eval nodeValue5489 x + ((8 : ℝ) * Sparse.eval nodeValue5499 x + 0))))

noncomputable def reducedSource27 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5424 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5477 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + ((4 : ℝ) * Sparse.eval nodeValue5482 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((2 : ℝ) * Sparse.eval nodeValue5497 x + ((4 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5500 x + ((1 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))

noncomputable def reducedSource28 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4096 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5452 x + ((3 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5485 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((1 : ℝ) * Sparse.eval nodeValue5489 x + ((4 : ℝ) * Sparse.eval nodeValue5490 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + ((1 : ℝ) * Sparse.eval nodeValue5498 x + ((4 : ℝ) * Sparse.eval nodeValue5499 x + ((2 : ℝ) * Sparse.eval nodeValue5500 x + ((2 : ℝ) * Sparse.eval nodeValue5501 x + 0))))))))))))))))

noncomputable def reducedSource29 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4091 x + ((4 : ℝ) * Sparse.eval nodeValue4092 x + ((4 : ℝ) * Sparse.eval nodeValue4093 x + ((2 : ℝ) * Sparse.eval nodeValue4095 x + ((8 : ℝ) * Sparse.eval nodeValue4096 x + ((4 : ℝ) * Sparse.eval nodeValue4097 x + 0)))))

noncomputable def reducedSource30 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1092 x + ((3 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource31 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1067 x + ((1 : ℝ) * Sparse.eval nodeValue1069 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

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

noncomputable def reducedSource198 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1006 x + ((1 : ℝ) * Sparse.eval nodeValue1010 x + ((1 : ℝ) * Sparse.eval nodeValue1011 x + ((1 : ℝ) * Sparse.eval nodeValue1084 x + ((2 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2408 x + ((1 : ℝ) * Sparse.eval nodeValue2409 x + ((2 : ℝ) * Sparse.eval nodeValue2463 x + ((2 : ℝ) * Sparse.eval nodeValue2465 x + ((2 : ℝ) * Sparse.eval nodeValue2466 x + ((2 : ℝ) * Sparse.eval nodeValue2513 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

noncomputable def reducedSource199 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1184 x + ((1 : ℝ) * Sparse.eval nodeValue1186 x + ((1 : ℝ) * Sparse.eval nodeValue1192 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((2 : ℝ) * Sparse.eval nodeValue1610 x + ((1 : ℝ) * Sparse.eval nodeValue1628 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((2 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((2 : ℝ) * Sparse.eval nodeValue2906 x + ((2 : ℝ) * Sparse.eval nodeValue2910 x + ((2 : ℝ) * Sparse.eval nodeValue2952 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((2 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0))))))))))))))))))))

noncomputable def reducedSource201 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1282 x + ((2 : ℝ) * Sparse.eval nodeValue1422 x + ((1 : ℝ) * Sparse.eval nodeValue1424 x + ((1 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource202 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1436 x + ((2 : ℝ) * Sparse.eval nodeValue2759 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource203 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1283 x + ((2 : ℝ) * Sparse.eval nodeValue2582 x + ((1 : ℝ) * Sparse.eval nodeValue2651 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource204 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1422 x + ((1 : ℝ) * Sparse.eval nodeValue2580 x + ((1 : ℝ) * Sparse.eval nodeValue2582 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource205 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1280 x + ((1 : ℝ) * Sparse.eval nodeValue2580 x + ((1 : ℝ) * Sparse.eval nodeValue2647 x + ((1 : ℝ) * Sparse.eval nodeValue2759 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource206 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1280 x + ((1 : ℝ) * Sparse.eval nodeValue1282 x + ((1 : ℝ) * Sparse.eval nodeValue1283 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource207 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1060 x + ((1 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue1062 x + ((1 : ℝ) * Sparse.eval nodeValue1088 x + ((2 : ℝ) * Sparse.eval nodeValue2496 x + ((2 : ℝ) * Sparse.eval nodeValue2497 x + ((2 : ℝ) * Sparse.eval nodeValue2498 x + ((2 : ℝ) * Sparse.eval nodeValue2516 x + ((2 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue2642 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((2 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2771 x + ((2 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))))))))))

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

noncomputable def reducedSource1971 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4363 x + ((1 : ℝ) * Sparse.eval nodeValue4365 x + ((2 : ℝ) * Sparse.eval nodeValue4368 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4695 x + ((1 : ℝ) * Sparse.eval nodeValue4697 x + ((2 : ℝ) * Sparse.eval nodeValue4700 x + ((1 : ℝ) * Sparse.eval nodeValue4771 x + ((2 : ℝ) * Sparse.eval nodeValue4773 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4863 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((2 : ℝ) * Sparse.eval nodeValue4867 x + ((2 : ℝ) * Sparse.eval nodeValue4868 x + ((2 : ℝ) * Sparse.eval nodeValue4874 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5279 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5291 x + 0))))))))))))))))))))

noncomputable def reducedSource1972 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1319 x + ((1 : ℝ) * Sparse.eval nodeValue1320 x + ((2 : ℝ) * Sparse.eval nodeValue1321 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + ((1 : ℝ) * Sparse.eval nodeValue2895 x + ((1 : ℝ) * Sparse.eval nodeValue2899 x + ((2 : ℝ) * Sparse.eval nodeValue2966 x + ((1 : ℝ) * Sparse.eval nodeValue3066 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((1 : ℝ) * Sparse.eval nodeValue3079 x + ((2 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3130 x + ((2 : ℝ) * Sparse.eval nodeValue3131 x + ((2 : ℝ) * Sparse.eval nodeValue3163 x + ((1 : ℝ) * Sparse.eval nodeValue3179 x + ((2 : ℝ) * Sparse.eval nodeValue3180 x + ((2 : ℝ) * Sparse.eval nodeValue3185 x + ((2 : ℝ) * Sparse.eval nodeValue3187 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource1973 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1697 x + ((1 : ℝ) * Sparse.eval nodeValue1704 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((2 : ℝ) * Sparse.eval nodeValue1712 x + ((1 : ℝ) * Sparse.eval nodeValue2189 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((2 : ℝ) * Sparse.eval nodeValue2194 x + ((1 : ℝ) * Sparse.eval nodeValue2231 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2239 x + ((2 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2249 x + ((2 : ℝ) * Sparse.eval nodeValue2251 x + ((2 : ℝ) * Sparse.eval nodeValue2261 x + ((2 : ℝ) * Sparse.eval nodeValue2264 x + ((2 : ℝ) * Sparse.eval nodeValue2276 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2748 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((2 : ℝ) * Sparse.eval nodeValue2765 x + 0))))))))))))))))))))

noncomputable def reducedSource1976 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4230 x + ((1 : ℝ) * Sparse.eval nodeValue4231 x + ((2 : ℝ) * Sparse.eval nodeValue4234 x + ((1 : ℝ) * Sparse.eval nodeValue4255 x + ((1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4678 x + ((2 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4720 x + ((2 : ℝ) * Sparse.eval nodeValue4722 x + ((1 : ℝ) * Sparse.eval nodeValue4731 x + ((2 : ℝ) * Sparse.eval nodeValue4798 x + ((2 : ℝ) * Sparse.eval nodeValue4800 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((2 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + 0))))))))))))))))))))

noncomputable def reducedSource1977 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue730 x + ((1 : ℝ) * Sparse.eval nodeValue731 x + ((2 : ℝ) * Sparse.eval nodeValue734 x + ((1 : ℝ) * Sparse.eval nodeValue823 x + ((1 : ℝ) * Sparse.eval nodeValue1802 x + ((1 : ℝ) * Sparse.eval nodeValue1804 x + ((2 : ℝ) * Sparse.eval nodeValue1810 x + ((1 : ℝ) * Sparse.eval nodeValue1874 x + ((2 : ℝ) * Sparse.eval nodeValue1876 x + ((1 : ℝ) * Sparse.eval nodeValue1921 x + ((2 : ℝ) * Sparse.eval nodeValue2018 x + ((2 : ℝ) * Sparse.eval nodeValue2075 x + ((2 : ℝ) * Sparse.eval nodeValue2082 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue3736 x + ((1 : ℝ) * Sparse.eval nodeValue3786 x + ((2 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + 0))))))))))))))))))))

noncomputable def reducedSource1978 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4435 x + ((1 : ℝ) * Sparse.eval nodeValue4437 x + ((1 : ℝ) * Sparse.eval nodeValue4443 x + ((2 : ℝ) * Sparse.eval nodeValue4452 x + ((1 : ℝ) * Sparse.eval nodeValue4791 x + ((1 : ℝ) * Sparse.eval nodeValue4794 x + ((2 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4848 x + ((2 : ℝ) * Sparse.eval nodeValue4850 x + ((1 : ℝ) * Sparse.eval nodeValue4851 x + ((2 : ℝ) * Sparse.eval nodeValue4855 x + ((2 : ℝ) * Sparse.eval nodeValue4860 x + ((2 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4879 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((2 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + 0))))))))))))))))))))

noncomputable def reducedSource1979 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1877 x + ((2 : ℝ) * Sparse.eval nodeValue1879 x + ((1 : ℝ) * Sparse.eval nodeValue1912 x + ((1 : ℝ) * Sparse.eval nodeValue2077 x + ((1 : ℝ) * Sparse.eval nodeValue3446 x + ((-1 : ℝ) * Sparse.eval nodeValue4079 x + 0)))))

noncomputable def reducedSource1980 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4331 x + ((2 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4351 x + ((1 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4667 x + ((2 : ℝ) * Sparse.eval nodeValue4668 x + ((1 : ℝ) * Sparse.eval nodeValue4685 x + ((1 : ℝ) * Sparse.eval nodeValue4765 x + ((2 : ℝ) * Sparse.eval nodeValue4775 x + ((2 : ℝ) * Sparse.eval nodeValue4793 x + ((2 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue5231 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5263 x + ((2 : ℝ) * Sparse.eval nodeValue5265 x + 0))))))))))))))))))))

noncomputable def reducedSource1981 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1680 x + ((1 : ℝ) * Sparse.eval nodeValue1684 x + ((1 : ℝ) * Sparse.eval nodeValue1737 x + ((2 : ℝ) * Sparse.eval nodeValue2154 x + ((1 : ℝ) * Sparse.eval nodeValue2156 x + ((1 : ℝ) * Sparse.eval nodeValue2160 x + ((1 : ℝ) * Sparse.eval nodeValue2179 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((2 : ℝ) * Sparse.eval nodeValue2211 x + ((2 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue2214 x + ((2 : ℝ) * Sparse.eval nodeValue2219 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2275 x + ((2 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2676 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((2 : ℝ) * Sparse.eval nodeValue2730 x + 0))))))))))))))))))))

noncomputable def reducedSource1982 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1793 x + ((2 : ℝ) * Sparse.eval nodeValue1794 x + ((1 : ℝ) * Sparse.eval nodeValue1811 x + ((1 : ℝ) * Sparse.eval nodeValue2023 x + ((1 : ℝ) * Sparse.eval nodeValue3378 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource1983 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4199 x + ((2 : ℝ) * Sparse.eval nodeValue4200 x + ((1 : ℝ) * Sparse.eval nodeValue4217 x + ((1 : ℝ) * Sparse.eval nodeValue4252 x + ((1 : ℝ) * Sparse.eval nodeValue4633 x + ((2 : ℝ) * Sparse.eval nodeValue4634 x + ((1 : ℝ) * Sparse.eval nodeValue4648 x + ((1 : ℝ) * Sparse.eval nodeValue4764 x + ((2 : ℝ) * Sparse.eval nodeValue4766 x + ((2 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4826 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + 0))))))))))))))))))))

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

noncomputable def reducedSource1984 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4327 x + ((1 : ℝ) * Sparse.eval nodeValue4329 x + ((1 : ℝ) * Sparse.eval nodeValue4332 x + ((1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4664 x + ((1 : ℝ) * Sparse.eval nodeValue4666 x + ((1 : ℝ) * Sparse.eval nodeValue4668 x + ((1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4772 x + ((1 : ℝ) * Sparse.eval nodeValue4774 x + ((1 : ℝ) * Sparse.eval nodeValue4775 x + ((1 : ℝ) * Sparse.eval nodeValue4792 x + ((1 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5255 x + ((1 : ℝ) * Sparse.eval nodeValue5256 x + ((1 : ℝ) * Sparse.eval nodeValue5257 x + ((1 : ℝ) * Sparse.eval nodeValue5271 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1985 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1327 x + ((1 : ℝ) * Sparse.eval nodeValue1328 x + ((1 : ℝ) * Sparse.eval nodeValue1331 x + ((1 : ℝ) * Sparse.eval nodeValue1339 x + ((1 : ℝ) * Sparse.eval nodeValue1411 x + ((1 : ℝ) * Sparse.eval nodeValue2423 x + ((1 : ℝ) * Sparse.eval nodeValue2430 x + ((1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2574 x + ((1 : ℝ) * Sparse.eval nodeValue3084 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3087 x + ((1 : ℝ) * Sparse.eval nodeValue3091 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3133 x + ((1 : ℝ) * Sparse.eval nodeValue3135 x + ((1 : ℝ) * Sparse.eval nodeValue3139 x + ((1 : ℝ) * Sparse.eval nodeValue3162 x + ((1 : ℝ) * Sparse.eval nodeValue3164 x + ((1 : ℝ) * Sparse.eval nodeValue3184 x + ((1 : ℝ) * Sparse.eval nodeValue3199 x + ((1 : ℝ) * Sparse.eval nodeValue3203 x + ((2 : ℝ) * Sparse.eval nodeValue3204 x + ((1 : ℝ) * Sparse.eval nodeValue3207 x + ((1 : ℝ) * Sparse.eval nodeValue3212 x + ((1 : ℝ) * Sparse.eval nodeValue3213 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((1 : ℝ) * Sparse.eval nodeValue3228 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1986 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1670 x + ((1 : ℝ) * Sparse.eval nodeValue1671 x + ((1 : ℝ) * Sparse.eval nodeValue1673 x + ((1 : ℝ) * Sparse.eval nodeValue1678 x + ((1 : ℝ) * Sparse.eval nodeValue1724 x + ((1 : ℝ) * Sparse.eval nodeValue2147 x + ((1 : ℝ) * Sparse.eval nodeValue2148 x + ((1 : ℝ) * Sparse.eval nodeValue2150 x + ((1 : ℝ) * Sparse.eval nodeValue2154 x + ((1 : ℝ) * Sparse.eval nodeValue2198 x + ((1 : ℝ) * Sparse.eval nodeValue2199 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((2 : ℝ) * Sparse.eval nodeValue2202 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((1 : ℝ) * Sparse.eval nodeValue2211 x + ((1 : ℝ) * Sparse.eval nodeValue2213 x + ((1 : ℝ) * Sparse.eval nodeValue2214 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2225 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((1 : ℝ) * Sparse.eval nodeValue2260 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2263 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2718 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource1987 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1790 x + ((1 : ℝ) * Sparse.eval nodeValue1792 x + ((1 : ℝ) * Sparse.eval nodeValue1794 x + ((1 : ℝ) * Sparse.eval nodeValue1805 x + ((1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue3376 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource1988 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4196 x + ((1 : ℝ) * Sparse.eval nodeValue4197 x + ((1 : ℝ) * Sparse.eval nodeValue4201 x + ((1 : ℝ) * Sparse.eval nodeValue4210 x + ((1 : ℝ) * Sparse.eval nodeValue4249 x + ((1 : ℝ) * Sparse.eval nodeValue4631 x + ((1 : ℝ) * Sparse.eval nodeValue4632 x + ((1 : ℝ) * Sparse.eval nodeValue4635 x + ((1 : ℝ) * Sparse.eval nodeValue4642 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4763 x + ((1 : ℝ) * Sparse.eval nodeValue4767 x + ((1 : ℝ) * Sparse.eval nodeValue4779 x + ((1 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4787 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource1989 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4397 x + ((1 : ℝ) * Sparse.eval nodeValue4400 x + ((1 : ℝ) * Sparse.eval nodeValue4417 x + ((1 : ℝ) * Sparse.eval nodeValue4449 x + ((1 : ℝ) * Sparse.eval nodeValue4736 x + ((1 : ℝ) * Sparse.eval nodeValue4737 x + ((1 : ℝ) * Sparse.eval nodeValue4739 x + ((1 : ℝ) * Sparse.eval nodeValue4740 x + ((1 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4799 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4813 x + ((1 : ℝ) * Sparse.eval nodeValue4815 x + ((1 : ℝ) * Sparse.eval nodeValue4816 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4849 x + ((1 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue4852 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5145 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((1 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1990 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4326 x + ((2 : ℝ) * Sparse.eval nodeValue4328 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4457 x + ((1 : ℝ) * Sparse.eval nodeValue4663 x + ((2 : ℝ) * Sparse.eval nodeValue4665 x + ((1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4771 x + ((2 : ℝ) * Sparse.eval nodeValue4773 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((2 : ℝ) * Sparse.eval nodeValue4804 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((2 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + 0))))))))))))))))))))

noncomputable def reducedSource1991 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1329 x + ((2 : ℝ) * Sparse.eval nodeValue1330 x + ((1 : ℝ) * Sparse.eval nodeValue1341 x + ((1 : ℝ) * Sparse.eval nodeValue1414 x + ((1 : ℝ) * Sparse.eval nodeValue2890 x + ((1 : ℝ) * Sparse.eval nodeValue2895 x + ((2 : ℝ) * Sparse.eval nodeValue2941 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3066 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((2 : ℝ) * Sparse.eval nodeValue3134 x + ((1 : ℝ) * Sparse.eval nodeValue3140 x + ((2 : ℝ) * Sparse.eval nodeValue3163 x + ((1 : ℝ) * Sparse.eval nodeValue3185 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((2 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((2 : ℝ) * Sparse.eval nodeValue3214 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + ((2 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource1992 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1663 x + ((1 : ℝ) * Sparse.eval nodeValue1664 x + ((2 : ℝ) * Sparse.eval nodeValue1667 x + ((1 : ℝ) * Sparse.eval nodeValue1707 x + ((1 : ℝ) * Sparse.eval nodeValue2140 x + ((1 : ℝ) * Sparse.eval nodeValue2141 x + ((2 : ℝ) * Sparse.eval nodeValue2144 x + ((1 : ℝ) * Sparse.eval nodeValue2189 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((2 : ℝ) * Sparse.eval nodeValue2194 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((2 : ℝ) * Sparse.eval nodeValue2203 x + ((2 : ℝ) * Sparse.eval nodeValue2205 x + ((2 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2242 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((2 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + 0))))))))))))))))))))

noncomputable def reducedSource1993 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4195 x + ((2 : ℝ) * Sparse.eval nodeValue4197 x + ((1 : ℝ) * Sparse.eval nodeValue4207 x + ((1 : ℝ) * Sparse.eval nodeValue4248 x + ((1 : ℝ) * Sparse.eval nodeValue4630 x + ((2 : ℝ) * Sparse.eval nodeValue4632 x + ((1 : ℝ) * Sparse.eval nodeValue4640 x + ((1 : ℝ) * Sparse.eval nodeValue4759 x + ((2 : ℝ) * Sparse.eval nodeValue4763 x + ((2 : ℝ) * Sparse.eval nodeValue4778 x + ((4 : ℝ) * Sparse.eval nodeValue4782 x + ((3 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4887 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5415 x + ((2 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + 0))))))))))))))))))

noncomputable def reducedSource1994 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4390 x + ((1 : ℝ) * Sparse.eval nodeValue4392 x + ((2 : ℝ) * Sparse.eval nodeValue4396 x + ((1 : ℝ) * Sparse.eval nodeValue4435 x + ((1 : ℝ) * Sparse.eval nodeValue4728 x + ((1 : ℝ) * Sparse.eval nodeValue4731 x + ((2 : ℝ) * Sparse.eval nodeValue4736 x + ((2 : ℝ) * Sparse.eval nodeValue4797 x + ((2 : ℝ) * Sparse.eval nodeValue4798 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4812 x + ((1 : ℝ) * Sparse.eval nodeValue4815 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4848 x + ((1 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((2 : ℝ) * Sparse.eval nodeValue5144 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + 0))))))))))))))))))))

noncomputable def reducedSource1995 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4345 x + ((1 : ℝ) * Sparse.eval nodeValue4353 x + ((1 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4357 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4680 x + ((1 : ℝ) * Sparse.eval nodeValue4687 x + ((1 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4690 x + ((1 : ℝ) * Sparse.eval nodeValue4765 x + ((1 : ℝ) * Sparse.eval nodeValue4766 x + ((1 : ℝ) * Sparse.eval nodeValue4768 x + ((1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4808 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4816 x + ((1 : ℝ) * Sparse.eval nodeValue4819 x + ((1 : ℝ) * Sparse.eval nodeValue4821 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((1 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1996 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1668 x + ((1 : ℝ) * Sparse.eval nodeValue1681 x + ((1 : ℝ) * Sparse.eval nodeValue1682 x + ((1 : ℝ) * Sparse.eval nodeValue1686 x + ((1 : ℝ) * Sparse.eval nodeValue1739 x + ((1 : ℝ) * Sparse.eval nodeValue2145 x + ((1 : ℝ) * Sparse.eval nodeValue2157 x + ((1 : ℝ) * Sparse.eval nodeValue2158 x + ((1 : ℝ) * Sparse.eval nodeValue2162 x + ((1 : ℝ) * Sparse.eval nodeValue2177 x + ((1 : ℝ) * Sparse.eval nodeValue2178 x + ((1 : ℝ) * Sparse.eval nodeValue2179 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2196 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2221 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1997 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1806 x + ((1 : ℝ) * Sparse.eval nodeValue1813 x + ((1 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue1816 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource1998 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4407 x + ((1 : ℝ) * Sparse.eval nodeValue4410 x + ((1 : ℝ) * Sparse.eval nodeValue4412 x + ((1 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4471 x + ((1 : ℝ) * Sparse.eval nodeValue4740 x + ((1 : ℝ) * Sparse.eval nodeValue4747 x + ((1 : ℝ) * Sparse.eval nodeValue4750 x + ((1 : ℝ) * Sparse.eval nodeValue4752 x + ((1 : ℝ) * Sparse.eval nodeValue4783 x + ((1 : ℝ) * Sparse.eval nodeValue4785 x + ((1 : ℝ) * Sparse.eval nodeValue4787 x + ((1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4806 x + ((1 : ℝ) * Sparse.eval nodeValue4813 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4836 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4840 x + ((1 : ℝ) * Sparse.eval nodeValue4842 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4870 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5138 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5173 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource1999 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4342 x + ((1 : ℝ) * Sparse.eval nodeValue4347 x + ((1 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4357 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((1 : ℝ) * Sparse.eval nodeValue4677 x + ((1 : ℝ) * Sparse.eval nodeValue4682 x + ((1 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4690 x + ((1 : ℝ) * Sparse.eval nodeValue4761 x + ((1 : ℝ) * Sparse.eval nodeValue4763 x + ((1 : ℝ) * Sparse.eval nodeValue4768 x + ((1 : ℝ) * Sparse.eval nodeValue4815 x + ((1 : ℝ) * Sparse.eval nodeValue4817 x + ((1 : ℝ) * Sparse.eval nodeValue4821 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5242 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + 0))))))))))))))))))))))))))))

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

noncomputable def reducedSource2000 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1665 x + ((1 : ℝ) * Sparse.eval nodeValue1675 x + ((1 : ℝ) * Sparse.eval nodeValue1676 x + ((1 : ℝ) * Sparse.eval nodeValue1682 x + ((1 : ℝ) * Sparse.eval nodeValue1728 x + ((1 : ℝ) * Sparse.eval nodeValue2142 x + ((1 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2158 x + ((1 : ℝ) * Sparse.eval nodeValue2174 x + ((1 : ℝ) * Sparse.eval nodeValue2175 x + ((1 : ℝ) * Sparse.eval nodeValue2178 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource2001 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1803 x + ((1 : ℝ) * Sparse.eval nodeValue1808 x + ((1 : ℝ) * Sparse.eval nodeValue1810 x + ((1 : ℝ) * Sparse.eval nodeValue1816 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource2002 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4210 x + ((1 : ℝ) * Sparse.eval nodeValue4212 x + ((1 : ℝ) * Sparse.eval nodeValue4213 x + ((1 : ℝ) * Sparse.eval nodeValue4224 x + ((1 : ℝ) * Sparse.eval nodeValue4265 x + ((1 : ℝ) * Sparse.eval nodeValue4642 x + ((1 : ℝ) * Sparse.eval nodeValue4644 x + ((1 : ℝ) * Sparse.eval nodeValue4645 x + ((1 : ℝ) * Sparse.eval nodeValue4654 x + ((1 : ℝ) * Sparse.eval nodeValue4709 x + ((1 : ℝ) * Sparse.eval nodeValue4710 x + ((1 : ℝ) * Sparse.eval nodeValue4717 x + ((1 : ℝ) * Sparse.eval nodeValue4737 x + ((1 : ℝ) * Sparse.eval nodeValue4787 x + ((2 : ℝ) * Sparse.eval nodeValue4788 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4832 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + 0))))))))))))))))))))))))))

noncomputable def reducedSource2003 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4397 x + ((1 : ℝ) * Sparse.eval nodeValue4402 x + ((1 : ℝ) * Sparse.eval nodeValue4404 x + ((1 : ℝ) * Sparse.eval nodeValue4424 x + ((1 : ℝ) * Sparse.eval nodeValue4453 x + ((1 : ℝ) * Sparse.eval nodeValue4737 x + ((1 : ℝ) * Sparse.eval nodeValue4742 x + ((1 : ℝ) * Sparse.eval nodeValue4745 x + ((1 : ℝ) * Sparse.eval nodeValue4752 x + ((1 : ℝ) * Sparse.eval nodeValue4780 x + ((1 : ℝ) * Sparse.eval nodeValue4782 x + ((1 : ℝ) * Sparse.eval nodeValue4787 x + ((2 : ℝ) * Sparse.eval nodeValue4799 x + ((1 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4828 x + ((1 : ℝ) * Sparse.eval nodeValue4829 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4836 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4861 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5135 x + ((1 : ℝ) * Sparse.eval nodeValue5164 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5170 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource2004 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4352 x + ((2 : ℝ) * Sparse.eval nodeValue4355 x + ((1 : ℝ) * Sparse.eval nodeValue4502 x + ((1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4686 x + ((2 : ℝ) * Sparse.eval nodeValue4689 x + ((1 : ℝ) * Sparse.eval nodeValue4764 x + ((2 : ℝ) * Sparse.eval nodeValue4767 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((3 : ℝ) * Sparse.eval nodeValue4838 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + 0)))))))))))))))))))

noncomputable def reducedSource2005 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4346 x + ((1 : ℝ) * Sparse.eval nodeValue4349 x + ((1 : ℝ) * Sparse.eval nodeValue4354 x + ((1 : ℝ) * Sparse.eval nodeValue4498 x + ((1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4760 x + ((1 : ℝ) * Sparse.eval nodeValue4763 x + ((1 : ℝ) * Sparse.eval nodeValue4766 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((1 : ℝ) * Sparse.eval nodeValue4804 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4835 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4841 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource2006 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4340 x + ((1 : ℝ) * Sparse.eval nodeValue4343 x + ((2 : ℝ) * Sparse.eval nodeValue4348 x + ((1 : ℝ) * Sparse.eval nodeValue4496 x + ((1 : ℝ) * Sparse.eval nodeValue4675 x + ((1 : ℝ) * Sparse.eval nodeValue4678 x + ((2 : ℝ) * Sparse.eval nodeValue4683 x + ((1 : ℝ) * Sparse.eval nodeValue4759 x + ((2 : ℝ) * Sparse.eval nodeValue4762 x + ((1 : ℝ) * Sparse.eval nodeValue4830 x + ((3 : ℝ) * Sparse.eval nodeValue4832 x + ((2 : ℝ) * Sparse.eval nodeValue4836 x + ((2 : ℝ) * Sparse.eval nodeValue4837 x + ((2 : ℝ) * Sparse.eval nodeValue4845 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue4897 x + ((1 : ℝ) * Sparse.eval nodeValue5222 x + ((1 : ℝ) * Sparse.eval nodeValue5239 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((2 : ℝ) * Sparse.eval nodeValue5261 x + 0)))))))))))))))))))

noncomputable def reducedSource2007 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1662 x + ((1 : ℝ) * Sparse.eval nodeValue1666 x + ((2 : ℝ) * Sparse.eval nodeValue1669 x + ((1 : ℝ) * Sparse.eval nodeValue1710 x + ((1 : ℝ) * Sparse.eval nodeValue2139 x + ((1 : ℝ) * Sparse.eval nodeValue2143 x + ((2 : ℝ) * Sparse.eval nodeValue2146 x + ((1 : ℝ) * Sparse.eval nodeValue2170 x + ((2 : ℝ) * Sparse.eval nodeValue2171 x + ((1 : ℝ) * Sparse.eval nodeValue2187 x + ((3 : ℝ) * Sparse.eval nodeValue2193 x + ((2 : ℝ) * Sparse.eval nodeValue2197 x + ((2 : ℝ) * Sparse.eval nodeValue2208 x + ((2 : ℝ) * Sparse.eval nodeValue2218 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2268 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2691 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((2 : ℝ) * Sparse.eval nodeValue2726 x + 0)))))))))))))))))))

noncomputable def reducedSource2008 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1801 x + ((1 : ℝ) * Sparse.eval nodeValue1804 x + ((2 : ℝ) * Sparse.eval nodeValue1809 x + ((1 : ℝ) * Sparse.eval nodeValue2052 x + ((1 : ℝ) * Sparse.eval nodeValue3389 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

noncomputable def reducedSource2009 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue918 x + ((1 : ℝ) * Sparse.eval nodeValue1801 x + ((1 : ℝ) * Sparse.eval nodeValue2050 x + ((3 : ℝ) * Sparse.eval nodeValue2052 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource2010 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4322 x + ((2 : ℝ) * Sparse.eval nodeValue4323 x + ((1 : ℝ) * Sparse.eval nodeValue4337 x + ((1 : ℝ) * Sparse.eval nodeValue4423 x + ((1 : ℝ) * Sparse.eval nodeValue4660 x + ((2 : ℝ) * Sparse.eval nodeValue4661 x + ((1 : ℝ) * Sparse.eval nodeValue4672 x + ((1 : ℝ) * Sparse.eval nodeValue4712 x + ((2 : ℝ) * Sparse.eval nodeValue4715 x + ((2 : ℝ) * Sparse.eval nodeValue4779 x + ((2 : ℝ) * Sparse.eval nodeValue4782 x + ((2 : ℝ) * Sparse.eval nodeValue4787 x + ((2 : ℝ) * Sparse.eval nodeValue4798 x + ((1 : ℝ) * Sparse.eval nodeValue4826 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue5058 x + ((1 : ℝ) * Sparse.eval nodeValue5123 x + ((2 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + 0))))))))))))))))))))

noncomputable def reducedSource2011 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4080 x + ((1 : ℝ) * Sparse.eval nodeValue4300 x + ((2 : ℝ) * Sparse.eval nodeValue4301 x + ((1 : ℝ) * Sparse.eval nodeValue4307 x + ((1 : ℝ) * Sparse.eval nodeValue4417 x + ((1 : ℝ) * Sparse.eval nodeValue4641 x + ((2 : ℝ) * Sparse.eval nodeValue4642 x + ((1 : ℝ) * Sparse.eval nodeValue4648 x + ((2 : ℝ) * Sparse.eval nodeValue4736 x + ((2 : ℝ) * Sparse.eval nodeValue4737 x + ((4 : ℝ) * Sparse.eval nodeValue4740 x + ((1 : ℝ) * Sparse.eval nodeValue4746 x + ((2 : ℝ) * Sparse.eval nodeValue4752 x + ((2 : ℝ) * Sparse.eval nodeValue4802 x + ((1 : ℝ) * Sparse.eval nodeValue4805 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4998 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + 0)))))))))))))))))))

noncomputable def reducedSource2012 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4063 x + ((1 : ℝ) * Sparse.eval nodeValue4064 x + ((2 : ℝ) * Sparse.eval nodeValue4065 x + ((1 : ℝ) * Sparse.eval nodeValue4069 x + ((1 : ℝ) * Sparse.eval nodeValue4073 x + ((1 : ℝ) * Sparse.eval nodeValue4074 x + ((2 : ℝ) * Sparse.eval nodeValue4075 x + ((1 : ℝ) * Sparse.eval nodeValue4077 x + ((2 : ℝ) * Sparse.eval nodeValue4078 x + ((1 : ℝ) * Sparse.eval nodeValue4079 x + ((5 : ℝ) * Sparse.eval nodeValue4080 x + ((2 : ℝ) * Sparse.eval nodeValue4081 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((1 : ℝ) * Sparse.eval nodeValue4083 x + ((2 : ℝ) * Sparse.eval nodeValue4084 x + ((1 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4090 x + ((1 : ℝ) * Sparse.eval nodeValue4091 x + ((2 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))))))))

noncomputable def reducedSource2013 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue3128 x + ((1 : ℝ) * Sparse.eval nodeValue3130 x + ((1 : ℝ) * Sparse.eval nodeValue3155 x + ((1 : ℝ) * Sparse.eval nodeValue3390 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource2014 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4541 x + ((2 : ℝ) * Sparse.eval nodeValue4544 x + ((1 : ℝ) * Sparse.eval nodeValue4622 x + ((2 : ℝ) * Sparse.eval nodeValue4968 x + ((2 : ℝ) * Sparse.eval nodeValue4971 x + ((2 : ℝ) * Sparse.eval nodeValue5148 x + ((4 : ℝ) * Sparse.eval nodeValue5149 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + 0)))))))))))))

noncomputable def reducedSource2015 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4341 x + ((2 : ℝ) * Sparse.eval nodeValue4344 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4939 x + ((2 : ℝ) * Sparse.eval nodeValue4941 x + ((4 : ℝ) * Sparse.eval nodeValue5134 x + ((2 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((4 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5257 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((2 : ℝ) * Sparse.eval nodeValue5482 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + 0)))))))))))))

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

noncomputable def reducedSource2016 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4540 x + ((3 : ℝ) * Sparse.eval nodeValue4542 x + ((1 : ℝ) * Sparse.eval nodeValue4618 x + ((3 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue4975 x + ((3 : ℝ) * Sparse.eval nodeValue5137 x + ((6 : ℝ) * Sparse.eval nodeValue5145 x + ((3 : ℝ) * Sparse.eval nodeValue5150 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((3 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5431 x + 0))))))))))))

noncomputable def reducedSource2017 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2688 x + ((1 : ℝ) * Sparse.eval nodeValue2690 x + ((3 : ℝ) * Sparse.eval nodeValue2700 x + ((3 : ℝ) * Sparse.eval nodeValue3257 x + ((1 : ℝ) * Sparse.eval nodeValue3304 x + ((3 : ℝ) * Sparse.eval nodeValue3521 x + ((1 : ℝ) * Sparse.eval nodeValue3546 x + ((3 : ℝ) * Sparse.eval nodeValue3554 x + ((6 : ℝ) * Sparse.eval nodeValue3562 x + ((3 : ℝ) * Sparse.eval nodeValue3581 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + ((1 : ℝ) * Sparse.eval nodeValue3867 x + ((3 : ℝ) * Sparse.eval nodeValue3875 x + 0))))))))))))

noncomputable def reducedSource2018 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4337 x + ((1 : ℝ) * Sparse.eval nodeValue4351 x + ((1 : ℝ) * Sparse.eval nodeValue4451 x + ((3 : ℝ) * Sparse.eval nodeValue4936 x + ((1 : ℝ) * Sparse.eval nodeValue4947 x + ((3 : ℝ) * Sparse.eval nodeValue5123 x + ((6 : ℝ) * Sparse.eval nodeValue5163 x + ((3 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((3 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + ((1 : ℝ) * Sparse.eval nodeValue5462 x + ((3 : ℝ) * Sparse.eval nodeValue5485 x + 0))))))))))))

noncomputable def reducedSource2019 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4364 x + ((2 : ℝ) * Sparse.eval nodeValue4366 x + ((1 : ℝ) * Sparse.eval nodeValue4456 x + ((2 : ℝ) * Sparse.eval nodeValue4696 x + ((2 : ℝ) * Sparse.eval nodeValue4698 x + ((2 : ℝ) * Sparse.eval nodeValue4851 x + ((4 : ℝ) * Sparse.eval nodeValue4852 x + ((4 : ℝ) * Sparse.eval nodeValue4866 x + ((2 : ℝ) * Sparse.eval nodeValue4869 x + ((2 : ℝ) * Sparse.eval nodeValue4887 x + ((2 : ℝ) * Sparse.eval nodeValue4893 x + ((1 : ℝ) * Sparse.eval nodeValue5278 x + ((2 : ℝ) * Sparse.eval nodeValue5281 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + 0)))))))))))))

noncomputable def reducedSource2020 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1703 x + ((1 : ℝ) * Sparse.eval nodeValue1706 x + ((2 : ℝ) * Sparse.eval nodeValue1711 x + ((2 : ℝ) * Sparse.eval nodeValue2238 x + ((2 : ℝ) * Sparse.eval nodeValue2240 x + ((2 : ℝ) * Sparse.eval nodeValue2243 x + ((2 : ℝ) * Sparse.eval nodeValue2248 x + ((4 : ℝ) * Sparse.eval nodeValue2250 x + ((4 : ℝ) * Sparse.eval nodeValue2260 x + ((2 : ℝ) * Sparse.eval nodeValue2263 x + ((2 : ℝ) * Sparse.eval nodeValue2275 x + ((1 : ℝ) * Sparse.eval nodeValue2747 x + ((2 : ℝ) * Sparse.eval nodeValue2750 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + 0)))))))))))))

noncomputable def reducedSource2021 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4230 x + ((2 : ℝ) * Sparse.eval nodeValue4232 x + ((1 : ℝ) * Sparse.eval nodeValue4252 x + ((2 : ℝ) * Sparse.eval nodeValue4676 x + ((2 : ℝ) * Sparse.eval nodeValue4679 x + ((4 : ℝ) * Sparse.eval nodeValue4798 x + ((2 : ℝ) * Sparse.eval nodeValue4805 x + ((2 : ℝ) * Sparse.eval nodeValue4826 x + ((2 : ℝ) * Sparse.eval nodeValue4865 x + ((4 : ℝ) * Sparse.eval nodeValue4866 x + ((2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + 0)))))))))))))

noncomputable def reducedSource2022 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4436 x + ((1 : ℝ) * Sparse.eval nodeValue4441 x + ((2 : ℝ) * Sparse.eval nodeValue4451 x + ((2 : ℝ) * Sparse.eval nodeValue4831 x + ((2 : ℝ) * Sparse.eval nodeValue4833 x + ((4 : ℝ) * Sparse.eval nodeValue4849 x + ((2 : ℝ) * Sparse.eval nodeValue4854 x + ((2 : ℝ) * Sparse.eval nodeValue4859 x + ((2 : ℝ) * Sparse.eval nodeValue4863 x + ((4 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4878 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((2 : ℝ) * Sparse.eval nodeValue5197 x + ((2 : ℝ) * Sparse.eval nodeValue5202 x + 0)))))))))))))

noncomputable def reducedSource2023 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4341 x + ((1 : ℝ) * Sparse.eval nodeValue4342 x + ((2 : ℝ) * Sparse.eval nodeValue4345 x + ((1 : ℝ) * Sparse.eval nodeValue4495 x + ((1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4677 x + ((2 : ℝ) * Sparse.eval nodeValue4680 x + ((1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4815 x + ((2 : ℝ) * Sparse.eval nodeValue4816 x + ((2 : ℝ) * Sparse.eval nodeValue4834 x + ((2 : ℝ) * Sparse.eval nodeValue4835 x + ((2 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4889 x + ((2 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + 0))))))))))))))))))))

noncomputable def reducedSource2024 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1664 x + ((1 : ℝ) * Sparse.eval nodeValue1665 x + ((2 : ℝ) * Sparse.eval nodeValue1668 x + ((1 : ℝ) * Sparse.eval nodeValue1708 x + ((1 : ℝ) * Sparse.eval nodeValue2141 x + ((1 : ℝ) * Sparse.eval nodeValue2142 x + ((2 : ℝ) * Sparse.eval nodeValue2145 x + ((1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2192 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((2 : ℝ) * Sparse.eval nodeValue2196 x + ((2 : ℝ) * Sparse.eval nodeValue2205 x + ((2 : ℝ) * Sparse.eval nodeValue2206 x + ((2 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2245 x + ((2 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + 0))))))))))))))))))))

noncomputable def reducedSource2025 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4063 x + ((1 : ℝ) * Sparse.eval nodeValue4068 x + ((4 : ℝ) * Sparse.eval nodeValue4073 x + ((12 : ℝ) * Sparse.eval nodeValue4080 x + ((4 : ℝ) * Sparse.eval nodeValue4083 x + ((1 : ℝ) * Sparse.eval nodeValue4087 x + ((4 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource2026 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue3131 x + ((1 : ℝ) * Sparse.eval nodeValue3365 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource2027 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2362 x + ((1 : ℝ) * Sparse.eval nodeValue3032 x + ((1 : ℝ) * Sparse.eval nodeValue3033 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource2028 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2343 x + ((1 : ℝ) * Sparse.eval nodeValue2819 x + ((1 : ℝ) * Sparse.eval nodeValue3673 x + ((1 : ℝ) * Sparse.eval nodeValue3699 x + ((1 : ℝ) * Sparse.eval nodeValue3705 x + ((1 : ℝ) * Sparse.eval nodeValue3706 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource2029 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2324 x + ((1 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue3676 x + ((1 : ℝ) * Sparse.eval nodeValue3685 x + ((1 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3692 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource2030 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2350 x + ((1 : ℝ) * Sparse.eval nodeValue3134 x + ((1 : ℝ) * Sparse.eval nodeValue3708 x + ((1 : ℝ) * Sparse.eval nodeValue3715 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3722 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource2031 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2824 x + ((1 : ℝ) * Sparse.eval nodeValue3709 x + ((1 : ℝ) * Sparse.eval nodeValue3716 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((1 : ℝ) * Sparse.eval nodeValue3922 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

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

noncomputable def reducedSource2032 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2351 x + ((1 : ℝ) * Sparse.eval nodeValue3135 x + ((1 : ℝ) * Sparse.eval nodeValue3709 x + ((1 : ℝ) * Sparse.eval nodeValue3716 x + ((2 : ℝ) * Sparse.eval nodeValue3721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource2033 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4691 x + ((2 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4874 x + ((4 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5372 x + ((4 : ℝ) * Sparse.eval nodeValue5384 x + ((4 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5441 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5449 x + 0))))))))))))

noncomputable def reducedSource2034 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue1814 x + ((1 : ℝ) * Sparse.eval nodeValue1817 x + ((2 : ℝ) * Sparse.eval nodeValue1819 x + ((2 : ℝ) * Sparse.eval nodeValue2115 x + ((4 : ℝ) * Sparse.eval nodeValue2817 x + ((1 : ℝ) * Sparse.eval nodeValue2820 x + ((2 : ℝ) * Sparse.eval nodeValue2968 x + ((2 : ℝ) * Sparse.eval nodeValue3708 x + ((4 : ℝ) * Sparse.eval nodeValue3732 x + ((4 : ℝ) * Sparse.eval nodeValue3739 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((2 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4037 x + 0))))))))))))

noncomputable def reducedSource2035 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue5232 x + ((2 : ℝ) * Sparse.eval nodeValue5235 x + ((4 : ℝ) * Sparse.eval nodeValue5238 x + ((2 : ℝ) * Sparse.eval nodeValue5297 x + ((8 : ℝ) * Sparse.eval nodeValue5355 x + ((2 : ℝ) * Sparse.eval nodeValue5371 x + ((2 : ℝ) * Sparse.eval nodeValue5376 x + ((2 : ℝ) * Sparse.eval nodeValue5390 x + 0)))))))

noncomputable def reducedSource2036 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4689 x + ((2 : ℝ) * Sparse.eval nodeValue4692 x + ((1 : ℝ) * Sparse.eval nodeValue4875 x + ((4 : ℝ) * Sparse.eval nodeValue4949 x + ((2 : ℝ) * Sparse.eval nodeValue4953 x + ((2 : ℝ) * Sparse.eval nodeValue4974 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5373 x + ((4 : ℝ) * Sparse.eval nodeValue5388 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5442 x + ((2 : ℝ) * Sparse.eval nodeValue5451 x + 0)))))))))))))

noncomputable def reducedSource2037 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1815 x + ((2 : ℝ) * Sparse.eval nodeValue1818 x + ((1 : ℝ) * Sparse.eval nodeValue2116 x + ((4 : ℝ) * Sparse.eval nodeValue2341 x + ((2 : ℝ) * Sparse.eval nodeValue2345 x + ((2 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2818 x + ((1 : ℝ) * Sparse.eval nodeValue2969 x + ((2 : ℝ) * Sparse.eval nodeValue3709 x + ((4 : ℝ) * Sparse.eval nodeValue3737 x + ((2 : ℝ) * Sparse.eval nodeValue3790 x + ((2 : ℝ) * Sparse.eval nodeValue3888 x + ((2 : ℝ) * Sparse.eval nodeValue3933 x + ((2 : ℝ) * Sparse.eval nodeValue4001 x + 0)))))))))))))

noncomputable def reducedSource2038 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5236 x + ((4 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5303 x + ((8 : ℝ) * Sparse.eval nodeValue5355 x + ((4 : ℝ) * Sparse.eval nodeValue5356 x + ((4 : ℝ) * Sparse.eval nodeValue5371 x + ((2 : ℝ) * Sparse.eval nodeValue5377 x + ((2 : ℝ) * Sparse.eval nodeValue5389 x + ((1 : ℝ) * Sparse.eval nodeValue5466 x + 0))))))))

noncomputable def reducedSource2039 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4668 x + ((1 : ℝ) * Sparse.eval nodeValue4669 x + ((1 : ℝ) * Sparse.eval nodeValue4670 x + ((1 : ℝ) * Sparse.eval nodeValue4690 x + ((1 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4931 x + ((1 : ℝ) * Sparse.eval nodeValue4934 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4957 x + ((1 : ℝ) * Sparse.eval nodeValue4959 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5339 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2040 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1794 x + ((1 : ℝ) * Sparse.eval nodeValue1795 x + ((1 : ℝ) * Sparse.eval nodeValue1796 x + ((1 : ℝ) * Sparse.eval nodeValue1816 x + ((1 : ℝ) * Sparse.eval nodeValue2094 x + ((1 : ℝ) * Sparse.eval nodeValue2350 x + ((1 : ℝ) * Sparse.eval nodeValue2352 x + ((1 : ℝ) * Sparse.eval nodeValue2359 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2801 x + ((1 : ℝ) * Sparse.eval nodeValue2802 x + ((1 : ℝ) * Sparse.eval nodeValue2819 x + ((1 : ℝ) * Sparse.eval nodeValue2824 x + ((1 : ℝ) * Sparse.eval nodeValue2829 x + ((1 : ℝ) * Sparse.eval nodeValue2943 x + ((1 : ℝ) * Sparse.eval nodeValue2990 x + ((1 : ℝ) * Sparse.eval nodeValue3710 x + ((1 : ℝ) * Sparse.eval nodeValue3711 x + ((1 : ℝ) * Sparse.eval nodeValue3724 x + ((1 : ℝ) * Sparse.eval nodeValue3727 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((1 : ℝ) * Sparse.eval nodeValue3738 x + ((1 : ℝ) * Sparse.eval nodeValue3783 x + ((1 : ℝ) * Sparse.eval nodeValue3831 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3937 x + ((1 : ℝ) * Sparse.eval nodeValue3941 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + ((1 : ℝ) * Sparse.eval nodeValue4035 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2041 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2154 x + ((1 : ℝ) * Sparse.eval nodeValue2155 x + ((1 : ℝ) * Sparse.eval nodeValue2158 x + ((1 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3417 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3509 x + ((1 : ℝ) * Sparse.eval nodeValue3512 x + ((1 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((1 : ℝ) * Sparse.eval nodeValue3754 x + ((1 : ℝ) * Sparse.eval nodeValue3757 x + ((1 : ℝ) * Sparse.eval nodeValue3760 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2042 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2348 x + ((1 : ℝ) * Sparse.eval nodeValue3133 x + ((1 : ℝ) * Sparse.eval nodeValue3671 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((1 : ℝ) * Sparse.eval nodeValue3720 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource2043 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2321 x + ((1 : ℝ) * Sparse.eval nodeValue2798 x + ((1 : ℝ) * Sparse.eval nodeValue3674 x + ((1 : ℝ) * Sparse.eval nodeValue3689 x + ((1 : ℝ) * Sparse.eval nodeValue3691 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource2044 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2356 x + ((1 : ℝ) * Sparse.eval nodeValue3138 x + ((1 : ℝ) * Sparse.eval nodeValue3674 x + ((1 : ℝ) * Sparse.eval nodeValue3693 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((1 : ℝ) * Sparse.eval nodeValue3733 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource2045 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4692 x + ((1 : ℝ) * Sparse.eval nodeValue4693 x + ((2 : ℝ) * Sparse.eval nodeValue4703 x + ((1 : ℝ) * Sparse.eval nodeValue4704 x + ((1 : ℝ) * Sparse.eval nodeValue4705 x + ((1 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4884 x + ((2 : ℝ) * Sparse.eval nodeValue4945 x + ((2 : ℝ) * Sparse.eval nodeValue4976 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((1 : ℝ) * Sparse.eval nodeValue5206 x + ((2 : ℝ) * Sparse.eval nodeValue5215 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((2 : ℝ) * Sparse.eval nodeValue5229 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5287 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0))))))))))))))))))))

noncomputable def reducedSource2046 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1829 x + ((1 : ℝ) * Sparse.eval nodeValue1830 x + ((1 : ℝ) * Sparse.eval nodeValue1831 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((2 : ℝ) * Sparse.eval nodeValue2362 x + ((1 : ℝ) * Sparse.eval nodeValue2363 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((2 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue2831 x + ((1 : ℝ) * Sparse.eval nodeValue2832 x + ((1 : ℝ) * Sparse.eval nodeValue3005 x + ((2 : ℝ) * Sparse.eval nodeValue3083 x + ((2 : ℝ) * Sparse.eval nodeValue3092 x + ((2 : ℝ) * Sparse.eval nodeValue3094 x + ((2 : ℝ) * Sparse.eval nodeValue3106 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((2 : ℝ) * Sparse.eval nodeValue3144 x + ((1 : ℝ) * Sparse.eval nodeValue3216 x + 0))))))))))))))))))))

noncomputable def reducedSource2047 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2169 x + ((1 : ℝ) * Sparse.eval nodeValue2229 x + ((2 : ℝ) * Sparse.eval nodeValue2272 x + ((1 : ℝ) * Sparse.eval nodeValue2273 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue2286 x + ((2 : ℝ) * Sparse.eval nodeValue2653 x + ((2 : ℝ) * Sparse.eval nodeValue2658 x + ((2 : ℝ) * Sparse.eval nodeValue2659 x + ((2 : ℝ) * Sparse.eval nodeValue2672 x + ((2 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + 0))))))))))))))))))))

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

noncomputable def reducedSource2048 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4950 x + ((4 : ℝ) * Sparse.eval nodeValue4952 x + ((4 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5457 x + ((8 : ℝ) * Sparse.eval nodeValue5465 x + ((4 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))

noncomputable def reducedSource2049 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue2342 x + ((4 : ℝ) * Sparse.eval nodeValue2344 x + ((4 : ℝ) * Sparse.eval nodeValue2605 x + ((2 : ℝ) * Sparse.eval nodeValue3917 x + ((8 : ℝ) * Sparse.eval nodeValue3931 x + ((4 : ℝ) * Sparse.eval nodeValue4000 x + 0)))))

noncomputable def reducedSource2050 (x : Master → ℝ) : ℝ :=
  (16 : ℝ) * Sparse.eval nodeValue5356 x + ((8 : ℝ) * Sparse.eval nodeValue5371 x + ((4 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5458 x + 0)))

noncomputable def reducedSource2051 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4932 x + ((2 : ℝ) * Sparse.eval nodeValue4933 x + ((2 : ℝ) * Sparse.eval nodeValue4934 x + ((2 : ℝ) * Sparse.eval nodeValue4935 x + ((1 : ℝ) * Sparse.eval nodeValue4950 x + ((2 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue4958 x + ((1 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5337 x + ((1 : ℝ) * Sparse.eval nodeValue5340 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5459 x + ((1 : ℝ) * Sparse.eval nodeValue5463 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + 0))))))))))))))))))))

noncomputable def reducedSource2052 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3409 x + ((2 : ℝ) * Sparse.eval nodeValue3414 x + ((2 : ℝ) * Sparse.eval nodeValue3415 x + ((2 : ℝ) * Sparse.eval nodeValue3418 x + ((2 : ℝ) * Sparse.eval nodeValue3419 x + ((1 : ℝ) * Sparse.eval nodeValue3421 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3511 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((1 : ℝ) * Sparse.eval nodeValue3592 x + ((2 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3756 x + ((1 : ℝ) * Sparse.eval nodeValue3763 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((2 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3951 x + ((1 : ℝ) * Sparse.eval nodeValue3960 x + ((2 : ℝ) * Sparse.eval nodeValue3961 x + 0))))))))))))))))))))

noncomputable def reducedSource2053 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2822 x + ((1 : ℝ) * Sparse.eval nodeValue3672 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((1 : ℝ) * Sparse.eval nodeValue3779 x + ((1 : ℝ) * Sparse.eval nodeValue3920 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource2054 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2322 x + ((1 : ℝ) * Sparse.eval nodeValue2799 x + ((1 : ℝ) * Sparse.eval nodeValue3675 x + ((2 : ℝ) * Sparse.eval nodeValue3690 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource2055 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2827 x + ((1 : ℝ) * Sparse.eval nodeValue3675 x + ((1 : ℝ) * Sparse.eval nodeValue3694 x + ((1 : ℝ) * Sparse.eval nodeValue3790 x + ((1 : ℝ) * Sparse.eval nodeValue3929 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource2056 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((4 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4952 x + ((2 : ℝ) * Sparse.eval nodeValue4953 x + ((4 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue4979 x + ((2 : ℝ) * Sparse.eval nodeValue5111 x + ((2 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5335 x + ((4 : ℝ) * Sparse.eval nodeValue5367 x + ((4 : ℝ) * Sparse.eval nodeValue5368 x + ((2 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + 0))))))))))))

noncomputable def reducedSource2057 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue3412 x + ((1 : ℝ) * Sparse.eval nodeValue3422 x + ((2 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3485 x + ((4 : ℝ) * Sparse.eval nodeValue3595 x + ((1 : ℝ) * Sparse.eval nodeValue3596 x + ((2 : ℝ) * Sparse.eval nodeValue3631 x + ((2 : ℝ) * Sparse.eval nodeValue3753 x + ((4 : ℝ) * Sparse.eval nodeValue3766 x + ((4 : ℝ) * Sparse.eval nodeValue3767 x + ((2 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))

noncomputable def reducedSource2058 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4075 x + ((4 : ℝ) * Sparse.eval nodeValue4076 x + ((4 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4086 x + ((8 : ℝ) * Sparse.eval nodeValue4088 x + ((4 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource2059 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4685 x + ((1 : ℝ) * Sparse.eval nodeValue4686 x + ((2 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4869 x + ((1 : ℝ) * Sparse.eval nodeValue4967 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue5114 x + ((1 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5372 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5389 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((1 : ℝ) * Sparse.eval nodeValue5415 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((2 : ℝ) * Sparse.eval nodeValue5441 x + ((2 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5448 x + 0))))))))))))))))))))

noncomputable def reducedSource2060 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4678 x + ((2 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4766 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4865 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((2 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5336 x + ((2 : ℝ) * Sparse.eval nodeValue5355 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5417 x + ((2 : ℝ) * Sparse.eval nodeValue5432 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + 0))))))))))))))))))))

noncomputable def reducedSource2061 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5222 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5231 x + ((2 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5279 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((2 : ℝ) * Sparse.eval nodeValue5370 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + 0))))))))))))))))))))

noncomputable def reducedSource2062 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4689 x + ((1 : ℝ) * Sparse.eval nodeValue4866 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5373 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((1 : ℝ) * Sparse.eval nodeValue5387 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5390 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5416 x + ((1 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5440 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5450 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource2063 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue5226 x + ((2 : ℝ) * Sparse.eval nodeValue5228 x + ((2 : ℝ) * Sparse.eval nodeValue5229 x + ((2 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5288 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((2 : ℝ) * Sparse.eval nodeValue5368 x + ((2 : ℝ) * Sparse.eval nodeValue5369 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((2 : ℝ) * Sparse.eval nodeValue5380 x + ((2 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5465 x + 0))))))))))))))))

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

noncomputable def reducedSource2064 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4680 x + ((1 : ℝ) * Sparse.eval nodeValue4682 x + ((1 : ℝ) * Sparse.eval nodeValue4683 x + ((1 : ℝ) * Sparse.eval nodeValue4690 x + ((1 : ℝ) * Sparse.eval nodeValue4867 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4976 x + ((1 : ℝ) * Sparse.eval nodeValue5042 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5163 x + ((1 : ℝ) * Sparse.eval nodeValue5188 x + ((1 : ℝ) * Sparse.eval nodeValue5216 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5339 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5385 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5402 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5432 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2065 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2145 x + ((1 : ℝ) * Sparse.eval nodeValue2146 x + ((1 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2158 x + ((1 : ℝ) * Sparse.eval nodeValue2251 x + ((1 : ℝ) * Sparse.eval nodeValue2654 x + ((1 : ℝ) * Sparse.eval nodeValue2659 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue3462 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3564 x + ((1 : ℝ) * Sparse.eval nodeValue3760 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3795 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3802 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3850 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3868 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2066 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4660 x + ((2 : ℝ) * Sparse.eval nodeValue4661 x + ((1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4826 x + ((1 : ℝ) * Sparse.eval nodeValue4960 x + ((2 : ℝ) * Sparse.eval nodeValue4961 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue5030 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5148 x + ((2 : ℝ) * Sparse.eval nodeValue5333 x + ((2 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5386 x + ((2 : ℝ) * Sparse.eval nodeValue5388 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + 0))))))))))))))))))))

noncomputable def reducedSource2067 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4663 x + ((2 : ℝ) * Sparse.eval nodeValue4666 x + ((1 : ℝ) * Sparse.eval nodeValue4677 x + ((1 : ℝ) * Sparse.eval nodeValue4851 x + ((1 : ℝ) * Sparse.eval nodeValue4956 x + ((2 : ℝ) * Sparse.eval nodeValue4958 x + ((1 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue5114 x + ((2 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5137 x + ((2 : ℝ) * Sparse.eval nodeValue5373 x + ((2 : ℝ) * Sparse.eval nodeValue5377 x + ((2 : ℝ) * Sparse.eval nodeValue5379 x + ((2 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5422 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + 0))))))))))))))))))))

noncomputable def reducedSource2068 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2140 x + ((1 : ℝ) * Sparse.eval nodeValue2142 x + ((2 : ℝ) * Sparse.eval nodeValue2148 x + ((1 : ℝ) * Sparse.eval nodeValue2240 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((2 : ℝ) * Sparse.eval nodeValue3511 x + ((2 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3521 x + ((1 : ℝ) * Sparse.eval nodeValue3554 x + ((1 : ℝ) * Sparse.eval nodeValue3597 x + ((2 : ℝ) * Sparse.eval nodeValue3792 x + ((1 : ℝ) * Sparse.eval nodeValue3798 x + ((2 : ℝ) * Sparse.eval nodeValue3832 x + ((2 : ℝ) * Sparse.eval nodeValue3835 x + ((2 : ℝ) * Sparse.eval nodeValue3836 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3867 x + ((1 : ℝ) * Sparse.eval nodeValue3900 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + 0))))))))))))))))))))

noncomputable def reducedSource2069 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4664 x + ((1 : ℝ) * Sparse.eval nodeValue4665 x + ((1 : ℝ) * Sparse.eval nodeValue4668 x + ((1 : ℝ) * Sparse.eval nodeValue4680 x + ((1 : ℝ) * Sparse.eval nodeValue4852 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4957 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue5038 x + ((1 : ℝ) * Sparse.eval nodeValue5080 x + ((1 : ℝ) * Sparse.eval nodeValue5129 x + ((1 : ℝ) * Sparse.eval nodeValue5134 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5372 x + ((1 : ℝ) * Sparse.eval nodeValue5376 x + ((1 : ℝ) * Sparse.eval nodeValue5379 x + ((2 : ℝ) * Sparse.eval nodeValue5381 x + ((1 : ℝ) * Sparse.eval nodeValue5382 x + ((1 : ℝ) * Sparse.eval nodeValue5384 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5423 x + ((1 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5425 x + ((1 : ℝ) * Sparse.eval nodeValue5445 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource2070 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2144 x + ((1 : ℝ) * Sparse.eval nodeValue2145 x + ((1 : ℝ) * Sparse.eval nodeValue2147 x + ((1 : ℝ) * Sparse.eval nodeValue2154 x + ((1 : ℝ) * Sparse.eval nodeValue2250 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3453 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3509 x + ((1 : ℝ) * Sparse.eval nodeValue3514 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3754 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3791 x + ((1 : ℝ) * Sparse.eval nodeValue3793 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3807 x + ((1 : ℝ) * Sparse.eval nodeValue3811 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3832 x + ((1 : ℝ) * Sparse.eval nodeValue3833 x + ((2 : ℝ) * Sparse.eval nodeValue3834 x + ((1 : ℝ) * Sparse.eval nodeValue3837 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3866 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource2071 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4686 x + ((2 : ℝ) * Sparse.eval nodeValue4689 x + ((1 : ℝ) * Sparse.eval nodeValue4696 x + ((1 : ℝ) * Sparse.eval nodeValue4697 x + ((2 : ℝ) * Sparse.eval nodeValue4701 x + ((1 : ℝ) * Sparse.eval nodeValue4838 x + ((1 : ℝ) * Sparse.eval nodeValue4879 x + ((1 : ℝ) * Sparse.eval nodeValue5116 x + ((2 : ℝ) * Sparse.eval nodeValue5151 x + ((2 : ℝ) * Sparse.eval nodeValue5217 x + ((2 : ℝ) * Sparse.eval nodeValue5226 x + ((1 : ℝ) * Sparse.eval nodeValue5227 x + ((2 : ℝ) * Sparse.eval nodeValue5236 x + ((2 : ℝ) * Sparse.eval nodeValue5237 x + ((1 : ℝ) * Sparse.eval nodeValue5247 x + ((2 : ℝ) * Sparse.eval nodeValue5271 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5286 x + ((2 : ℝ) * Sparse.eval nodeValue5299 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + 0))))))))))))))))))))

noncomputable def reducedSource2072 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2150 x + ((1 : ℝ) * Sparse.eval nodeValue2165 x + ((2 : ℝ) * Sparse.eval nodeValue2166 x + ((1 : ℝ) * Sparse.eval nodeValue2227 x + ((1 : ℝ) * Sparse.eval nodeValue2238 x + ((1 : ℝ) * Sparse.eval nodeValue2239 x + ((1 : ℝ) * Sparse.eval nodeValue2246 x + ((2 : ℝ) * Sparse.eval nodeValue2257 x + ((1 : ℝ) * Sparse.eval nodeValue2655 x + ((2 : ℝ) * Sparse.eval nodeValue2656 x + ((2 : ℝ) * Sparse.eval nodeValue2669 x + ((1 : ℝ) * Sparse.eval nodeValue2671 x + ((2 : ℝ) * Sparse.eval nodeValue2681 x + ((2 : ℝ) * Sparse.eval nodeValue2682 x + ((2 : ℝ) * Sparse.eval nodeValue2684 x + ((1 : ℝ) * Sparse.eval nodeValue2703 x + ((2 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((1 : ℝ) * Sparse.eval nodeValue3023 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + 0))))))))))))))))))))

noncomputable def reducedSource2073 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4676 x + ((1 : ℝ) * Sparse.eval nodeValue4681 x + ((1 : ℝ) * Sparse.eval nodeValue4684 x + ((1 : ℝ) * Sparse.eval nodeValue4688 x + ((1 : ℝ) * Sparse.eval nodeValue4698 x + ((1 : ℝ) * Sparse.eval nodeValue4699 x + ((1 : ℝ) * Sparse.eval nodeValue4700 x + ((1 : ℝ) * Sparse.eval nodeValue4703 x + ((1 : ℝ) * Sparse.eval nodeValue4834 x + ((1 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue5035 x + ((1 : ℝ) * Sparse.eval nodeValue5110 x + ((1 : ℝ) * Sparse.eval nodeValue5140 x + ((1 : ℝ) * Sparse.eval nodeValue5215 x + ((1 : ℝ) * Sparse.eval nodeValue5216 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((1 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((1 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2074 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2141 x + ((1 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2157 x + ((1 : ℝ) * Sparse.eval nodeValue2205 x + ((1 : ℝ) * Sparse.eval nodeValue2248 x + ((1 : ℝ) * Sparse.eval nodeValue2249 x + ((1 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2256 x + ((1 : ℝ) * Sparse.eval nodeValue2272 x + ((1 : ℝ) * Sparse.eval nodeValue2652 x + ((1 : ℝ) * Sparse.eval nodeValue2653 x + ((1 : ℝ) * Sparse.eval nodeValue2654 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2685 x + ((1 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2075 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4947 x + ((2 : ℝ) * Sparse.eval nodeValue4948 x + ((4 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue5115 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5373 x + ((2 : ℝ) * Sparse.eval nodeValue5390 x + ((2 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((4 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5462 x + ((2 : ℝ) * Sparse.eval nodeValue5485 x + 0)))))))))))))

noncomputable def reducedSource2076 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4767 x + ((2 : ℝ) * Sparse.eval nodeValue4769 x + ((2 : ℝ) * Sparse.eval nodeValue4811 x + ((2 : ℝ) * Sparse.eval nodeValue4939 x + ((4 : ℝ) * Sparse.eval nodeValue4946 x + ((2 : ℝ) * Sparse.eval nodeValue5168 x + ((2 : ℝ) * Sparse.eval nodeValue5337 x + ((2 : ℝ) * Sparse.eval nodeValue5356 x + ((2 : ℝ) * Sparse.eval nodeValue5393 x + ((2 : ℝ) * Sparse.eval nodeValue5416 x + ((4 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((2 : ℝ) * Sparse.eval nodeValue5465 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + 0)))))))))))))

noncomputable def reducedSource2077 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4941 x + ((2 : ℝ) * Sparse.eval nodeValue4943 x + ((2 : ℝ) * Sparse.eval nodeValue4946 x + ((2 : ℝ) * Sparse.eval nodeValue4950 x + ((1 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((1 : ℝ) * Sparse.eval nodeValue5337 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5418 x + ((1 : ℝ) * Sparse.eval nodeValue5457 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + ((1 : ℝ) * Sparse.eval nodeValue5464 x + ((2 : ℝ) * Sparse.eval nodeValue5465 x + ((1 : ℝ) * Sparse.eval nodeValue5466 x + ((2 : ℝ) * Sparse.eval nodeValue5476 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((2 : ℝ) * Sparse.eval nodeValue5486 x + ((2 : ℝ) * Sparse.eval nodeValue5487 x + 0)))))))))))))))))))

noncomputable def reducedSource2078 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4942 x + ((2 : ℝ) * Sparse.eval nodeValue4944 x + ((2 : ℝ) * Sparse.eval nodeValue4945 x + ((2 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue5043 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((2 : ℝ) * Sparse.eval nodeValue5170 x + ((1 : ℝ) * Sparse.eval nodeValue5189 x + ((1 : ℝ) * Sparse.eval nodeValue5217 x + ((1 : ℝ) * Sparse.eval nodeValue5236 x + ((1 : ℝ) * Sparse.eval nodeValue5269 x + ((1 : ℝ) * Sparse.eval nodeValue5340 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5393 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5419 x + ((2 : ℝ) * Sparse.eval nodeValue5438 x + ((1 : ℝ) * Sparse.eval nodeValue5461 x + ((1 : ℝ) * Sparse.eval nodeValue5463 x + ((2 : ℝ) * Sparse.eval nodeValue5484 x + 0))))))))))))))))))))

noncomputable def reducedSource2079 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2656 x + ((2 : ℝ) * Sparse.eval nodeValue2658 x + ((1 : ℝ) * Sparse.eval nodeValue2682 x + ((1 : ℝ) * Sparse.eval nodeValue2736 x + ((2 : ℝ) * Sparse.eval nodeValue3407 x + ((2 : ℝ) * Sparse.eval nodeValue3413 x + ((2 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3465 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3542 x + ((2 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3763 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3797 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3842 x + ((2 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3960 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((2 : ℝ) * Sparse.eval nodeValue3983 x + 0))))))))))))))))))))

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

noncomputable def reducedSource208 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2603 x + ((2 : ℝ) * Sparse.eval nodeValue3050 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource209 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1374 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((2 : ℝ) * Sparse.eval nodeValue2978 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3056 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource210 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2597 x + ((1 : ℝ) * Sparse.eval nodeValue2973 x + ((1 : ℝ) * Sparse.eval nodeValue2978 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource211 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource212 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2062 x + ((2 : ℝ) * Sparse.eval nodeValue2879 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource213 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1210 x + ((1 : ℝ) * Sparse.eval nodeValue1211 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1230 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue2071 x + ((1 : ℝ) * Sparse.eval nodeValue2080 x + ((1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2860 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2876 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2922 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue2990 x + ((1 : ℝ) * Sparse.eval nodeValue2997 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3085 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3982 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource214 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2043 x + ((1 : ℝ) * Sparse.eval nodeValue2045 x + ((1 : ℝ) * Sparse.eval nodeValue2049 x + ((1 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue3285 x + ((1 : ℝ) * Sparse.eval nodeValue3287 x + ((1 : ℝ) * Sparse.eval nodeValue3295 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3478 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3516 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3525 x + ((1 : ℝ) * Sparse.eval nodeValue3527 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3560 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3575 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3852 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource215 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3903 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource216 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1214 x + ((1 : ℝ) * Sparse.eval nodeValue1218 x + ((1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue1263 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource217 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1263 x + ((1 : ℝ) * Sparse.eval nodeValue2568 x + ((1 : ℝ) * Sparse.eval nodeValue2634 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource218 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource219 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1214 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2616 x + ((1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue2720 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource220 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2544 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue2568 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource221 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1241 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource222 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2616 x + ((1 : ℝ) * Sparse.eval nodeValue2619 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2634 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource223 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1219 x + ((1 : ℝ) * Sparse.eval nodeValue2488 x + ((1 : ℝ) * Sparse.eval nodeValue2545 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

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

noncomputable def reducedSource2080 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4930 x + ((2 : ℝ) * Sparse.eval nodeValue4931 x + ((2 : ℝ) * Sparse.eval nodeValue4933 x + ((2 : ℝ) * Sparse.eval nodeValue4942 x + ((1 : ℝ) * Sparse.eval nodeValue5039 x + ((1 : ℝ) * Sparse.eval nodeValue5081 x + ((1 : ℝ) * Sparse.eval nodeValue5130 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5337 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5373 x + ((1 : ℝ) * Sparse.eval nodeValue5377 x + ((2 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5404 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((2 : ℝ) * Sparse.eval nodeValue5419 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5459 x + ((1 : ℝ) * Sparse.eval nodeValue5461 x + ((2 : ℝ) * Sparse.eval nodeValue5478 x + 0)))))))))))))))))))

noncomputable def reducedSource2081 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3406 x + ((2 : ℝ) * Sparse.eval nodeValue3407 x + ((2 : ℝ) * Sparse.eval nodeValue3408 x + ((2 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3456 x + ((1 : ℝ) * Sparse.eval nodeValue3482 x + ((1 : ℝ) * Sparse.eval nodeValue3520 x + ((2 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3756 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3792 x + ((2 : ℝ) * Sparse.eval nodeValue3798 x + ((1 : ℝ) * Sparse.eval nodeValue3815 x + ((2 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3835 x + ((2 : ℝ) * Sparse.eval nodeValue3842 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3951 x + ((1 : ℝ) * Sparse.eval nodeValue3973 x + ((2 : ℝ) * Sparse.eval nodeValue3974 x + 0)))))))))))))))))))

noncomputable def reducedSource2082 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4756 x + ((1 : ℝ) * Sparse.eval nodeValue4757 x + ((1 : ℝ) * Sparse.eval nodeValue4768 x + ((2 : ℝ) * Sparse.eval nodeValue4795 x + ((2 : ℝ) * Sparse.eval nodeValue4933 x + ((1 : ℝ) * Sparse.eval nodeValue4947 x + ((2 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4967 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5184 x + ((2 : ℝ) * Sparse.eval nodeValue5338 x + ((2 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5366 x + ((1 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + 0))))))))))))))))))))

noncomputable def reducedSource2083 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2176 x + ((1 : ℝ) * Sparse.eval nodeValue2178 x + ((1 : ℝ) * Sparse.eval nodeValue2181 x + ((2 : ℝ) * Sparse.eval nodeValue2213 x + ((2 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3416 x + ((1 : ℝ) * Sparse.eval nodeValue3477 x + ((2 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3524 x + ((1 : ℝ) * Sparse.eval nodeValue3585 x + ((2 : ℝ) * Sparse.eval nodeValue3755 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3765 x + ((2 : ℝ) * Sparse.eval nodeValue3768 x + ((2 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3810 x + ((2 : ℝ) * Sparse.eval nodeValue3812 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + 0))))))))))))))))))))

noncomputable def reducedSource2084 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4930 x + ((1 : ℝ) * Sparse.eval nodeValue4932 x + ((1 : ℝ) * Sparse.eval nodeValue4933 x + ((1 : ℝ) * Sparse.eval nodeValue4941 x + ((1 : ℝ) * Sparse.eval nodeValue4954 x + ((1 : ℝ) * Sparse.eval nodeValue4955 x + ((1 : ℝ) * Sparse.eval nodeValue4958 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue5040 x + ((1 : ℝ) * Sparse.eval nodeValue5067 x + ((1 : ℝ) * Sparse.eval nodeValue5073 x + ((1 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5185 x + ((1 : ℝ) * Sparse.eval nodeValue5338 x + ((1 : ℝ) * Sparse.eval nodeValue5340 x + ((1 : ℝ) * Sparse.eval nodeValue5348 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((1 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5366 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5401 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5470 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + ((1 : ℝ) * Sparse.eval nodeValue5472 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource2085 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3408 x + ((1 : ℝ) * Sparse.eval nodeValue3409 x + ((1 : ℝ) * Sparse.eval nodeValue3410 x + ((1 : ℝ) * Sparse.eval nodeValue3414 x + ((1 : ℝ) * Sparse.eval nodeValue3452 x + ((1 : ℝ) * Sparse.eval nodeValue3454 x + ((1 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((1 : ℝ) * Sparse.eval nodeValue3508 x + ((1 : ℝ) * Sparse.eval nodeValue3511 x + ((1 : ℝ) * Sparse.eval nodeValue3529 x + ((1 : ℝ) * Sparse.eval nodeValue3587 x + ((1 : ℝ) * Sparse.eval nodeValue3612 x + ((1 : ℝ) * Sparse.eval nodeValue3755 x + ((1 : ℝ) * Sparse.eval nodeValue3763 x + ((2 : ℝ) * Sparse.eval nodeValue3764 x + ((1 : ℝ) * Sparse.eval nodeValue3765 x + ((1 : ℝ) * Sparse.eval nodeValue3768 x + ((1 : ℝ) * Sparse.eval nodeValue3769 x + ((1 : ℝ) * Sparse.eval nodeValue3773 x + ((1 : ℝ) * Sparse.eval nodeValue3774 x + ((1 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((1 : ℝ) * Sparse.eval nodeValue3816 x + ((1 : ℝ) * Sparse.eval nodeValue3955 x + ((1 : ℝ) * Sparse.eval nodeValue3956 x + ((1 : ℝ) * Sparse.eval nodeValue3957 x + ((1 : ℝ) * Sparse.eval nodeValue3961 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource2086 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4929 x + ((2 : ℝ) * Sparse.eval nodeValue4931 x + ((1 : ℝ) * Sparse.eval nodeValue4939 x + ((1 : ℝ) * Sparse.eval nodeValue4956 x + ((2 : ℝ) * Sparse.eval nodeValue4957 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((1 : ℝ) * Sparse.eval nodeValue5072 x + ((1 : ℝ) * Sparse.eval nodeValue5112 x + ((2 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((2 : ℝ) * Sparse.eval nodeValue5339 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((2 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5400 x + ((1 : ℝ) * Sparse.eval nodeValue5405 x + ((2 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5471 x + 0))))))))))))))))))))

noncomputable def reducedSource2087 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3403 x + ((1 : ℝ) * Sparse.eval nodeValue3404 x + ((2 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3459 x + ((2 : ℝ) * Sparse.eval nodeValue3509 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((2 : ℝ) * Sparse.eval nodeValue3522 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3556 x + ((1 : ℝ) * Sparse.eval nodeValue3590 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((2 : ℝ) * Sparse.eval nodeValue3760 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((2 : ℝ) * Sparse.eval nodeValue3766 x + ((2 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3799 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3807 x + ((2 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((1 : ℝ) * Sparse.eval nodeValue3953 x + 0))))))))))))))))))))

noncomputable def reducedSource2088 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4775 x + ((1 : ℝ) * Sparse.eval nodeValue4776 x + ((1 : ℝ) * Sparse.eval nodeValue4777 x + ((1 : ℝ) * Sparse.eval nodeValue4821 x + ((1 : ℝ) * Sparse.eval nodeValue4856 x + ((1 : ℝ) * Sparse.eval nodeValue4942 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue4963 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue5105 x + ((1 : ℝ) * Sparse.eval nodeValue5198 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5338 x + ((1 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5360 x + ((1 : ℝ) * Sparse.eval nodeValue5361 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5397 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5412 x + ((1 : ℝ) * Sparse.eval nodeValue5421 x + ((1 : ℝ) * Sparse.eval nodeValue5436 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2089 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2211 x + ((1 : ℝ) * Sparse.eval nodeValue2212 x + ((1 : ℝ) * Sparse.eval nodeValue2217 x + ((1 : ℝ) * Sparse.eval nodeValue2223 x + ((1 : ℝ) * Sparse.eval nodeValue2274 x + ((1 : ℝ) * Sparse.eval nodeValue3407 x + ((1 : ℝ) * Sparse.eval nodeValue3417 x + ((1 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3553 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3570 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((1 : ℝ) * Sparse.eval nodeValue3754 x + ((1 : ℝ) * Sparse.eval nodeValue3755 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3762 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3770 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3796 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3873 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2090 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4940 x + ((1 : ℝ) * Sparse.eval nodeValue4944 x + ((1 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4951 x + ((1 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue4965 x + ((1 : ℝ) * Sparse.eval nodeValue4966 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5044 x + ((1 : ℝ) * Sparse.eval nodeValue5090 x + ((1 : ℝ) * Sparse.eval nodeValue5102 x + ((1 : ℝ) * Sparse.eval nodeValue5199 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((1 : ℝ) * Sparse.eval nodeValue5335 x + ((1 : ℝ) * Sparse.eval nodeValue5338 x + ((1 : ℝ) * Sparse.eval nodeValue5359 x + ((1 : ℝ) * Sparse.eval nodeValue5361 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5411 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5446 x + ((1 : ℝ) * Sparse.eval nodeValue5468 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5475 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2091 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3405 x + ((1 : ℝ) * Sparse.eval nodeValue3412 x + ((1 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3418 x + ((1 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3474 x + ((1 : ℝ) * Sparse.eval nodeValue3475 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3554 x + ((1 : ℝ) * Sparse.eval nodeValue3555 x + ((1 : ℝ) * Sparse.eval nodeValue3578 x + ((1 : ℝ) * Sparse.eval nodeValue3595 x + ((1 : ℝ) * Sparse.eval nodeValue3631 x + ((1 : ℝ) * Sparse.eval nodeValue3753 x + ((1 : ℝ) * Sparse.eval nodeValue3755 x + ((1 : ℝ) * Sparse.eval nodeValue3758 x + ((1 : ℝ) * Sparse.eval nodeValue3759 x + ((1 : ℝ) * Sparse.eval nodeValue3766 x + ((1 : ℝ) * Sparse.eval nodeValue3767 x + ((1 : ℝ) * Sparse.eval nodeValue3771 x + ((1 : ℝ) * Sparse.eval nodeValue3772 x + ((1 : ℝ) * Sparse.eval nodeValue3775 x + ((1 : ℝ) * Sparse.eval nodeValue3794 x + ((1 : ℝ) * Sparse.eval nodeValue3808 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3817 x + ((1 : ℝ) * Sparse.eval nodeValue3950 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((1 : ℝ) * Sparse.eval nodeValue3959 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2092 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4091 x + ((1 : ℝ) * Sparse.eval nodeValue4941 x + ((1 : ℝ) * Sparse.eval nodeValue4948 x + ((2 : ℝ) * Sparse.eval nodeValue4950 x + ((1 : ℝ) * Sparse.eval nodeValue4968 x + ((1 : ℝ) * Sparse.eval nodeValue4970 x + ((2 : ℝ) * Sparse.eval nodeValue4974 x + ((1 : ℝ) * Sparse.eval nodeValue5104 x + ((1 : ℝ) * Sparse.eval nodeValue5117 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((1 : ℝ) * Sparse.eval nodeValue5203 x + ((2 : ℝ) * Sparse.eval nodeValue5337 x + ((2 : ℝ) * Sparse.eval nodeValue5352 x + ((2 : ℝ) * Sparse.eval nodeValue5356 x + ((1 : ℝ) * Sparse.eval nodeValue5366 x + ((2 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((2 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + ((2 : ℝ) * Sparse.eval nodeValue5473 x + ((1 : ℝ) * Sparse.eval nodeValue5474 x + 0))))))))))))))))))))

noncomputable def reducedSource2093 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue4939 x + ((1 : ℝ) * Sparse.eval nodeValue4943 x + ((1 : ℝ) * Sparse.eval nodeValue4946 x + ((1 : ℝ) * Sparse.eval nodeValue4949 x + ((1 : ℝ) * Sparse.eval nodeValue4971 x + ((1 : ℝ) * Sparse.eval nodeValue4972 x + ((1 : ℝ) * Sparse.eval nodeValue4973 x + ((1 : ℝ) * Sparse.eval nodeValue4977 x + ((1 : ℝ) * Sparse.eval nodeValue5036 x + ((1 : ℝ) * Sparse.eval nodeValue5101 x + ((1 : ℝ) * Sparse.eval nodeValue5111 x + ((1 : ℝ) * Sparse.eval nodeValue5141 x + ((1 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5335 x + ((1 : ℝ) * Sparse.eval nodeValue5336 x + ((1 : ℝ) * Sparse.eval nodeValue5351 x + ((1 : ℝ) * Sparse.eval nodeValue5355 x + ((1 : ℝ) * Sparse.eval nodeValue5365 x + ((1 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5368 x + ((1 : ℝ) * Sparse.eval nodeValue5370 x + ((1 : ℝ) * Sparse.eval nodeValue5371 x + ((1 : ℝ) * Sparse.eval nodeValue5394 x + ((1 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5409 x + ((1 : ℝ) * Sparse.eval nodeValue5410 x + ((1 : ℝ) * Sparse.eval nodeValue5413 x + ((1 : ℝ) * Sparse.eval nodeValue5428 x + ((1 : ℝ) * Sparse.eval nodeValue5473 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource2094 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4763 x + ((1 : ℝ) * Sparse.eval nodeValue4769 x + ((1 : ℝ) * Sparse.eval nodeValue4770 x + ((2 : ℝ) * Sparse.eval nodeValue4846 x + ((1 : ℝ) * Sparse.eval nodeValue4938 x + ((2 : ℝ) * Sparse.eval nodeValue4945 x + ((1 : ℝ) * Sparse.eval nodeValue4975 x + ((2 : ℝ) * Sparse.eval nodeValue4976 x + ((1 : ℝ) * Sparse.eval nodeValue5099 x + ((1 : ℝ) * Sparse.eval nodeValue5205 x + ((2 : ℝ) * Sparse.eval nodeValue5215 x + ((2 : ℝ) * Sparse.eval nodeValue5238 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5242 x + ((2 : ℝ) * Sparse.eval nodeValue5248 x + ((2 : ℝ) * Sparse.eval nodeValue5274 x + ((2 : ℝ) * Sparse.eval nodeValue5275 x + ((1 : ℝ) * Sparse.eval nodeValue5277 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5287 x + 0))))))))))))))))))))

noncomputable def reducedSource2095 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2174 x + ((1 : ℝ) * Sparse.eval nodeValue2185 x + ((1 : ℝ) * Sparse.eval nodeValue2186 x + ((2 : ℝ) * Sparse.eval nodeValue2229 x + ((2 : ℝ) * Sparse.eval nodeValue2653 x + ((2 : ℝ) * Sparse.eval nodeValue2658 x + ((2 : ℝ) * Sparse.eval nodeValue2659 x + ((2 : ℝ) * Sparse.eval nodeValue2686 x + ((1 : ℝ) * Sparse.eval nodeValue2689 x + ((1 : ℝ) * Sparse.eval nodeValue2690 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((1 : ℝ) * Sparse.eval nodeValue2704 x + ((2 : ℝ) * Sparse.eval nodeValue2705 x + ((1 : ℝ) * Sparse.eval nodeValue2706 x + ((2 : ℝ) * Sparse.eval nodeValue2742 x + ((2 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3059 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + 0))))))))))))))))))))

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

noncomputable def reducedSource2096 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4090 x + ((1 : ℝ) * Sparse.eval nodeValue4927 x + ((2 : ℝ) * Sparse.eval nodeValue4928 x + ((1 : ℝ) * Sparse.eval nodeValue4936 x + ((1 : ℝ) * Sparse.eval nodeValue4960 x + ((2 : ℝ) * Sparse.eval nodeValue4961 x + ((1 : ℝ) * Sparse.eval nodeValue4969 x + ((1 : ℝ) * Sparse.eval nodeValue5029 x + ((2 : ℝ) * Sparse.eval nodeValue5050 x + ((1 : ℝ) * Sparse.eval nodeValue5058 x + ((1 : ℝ) * Sparse.eval nodeValue5192 x + ((2 : ℝ) * Sparse.eval nodeValue5332 x + ((2 : ℝ) * Sparse.eval nodeValue5341 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5349 x + ((1 : ℝ) * Sparse.eval nodeValue5363 x + ((1 : ℝ) * Sparse.eval nodeValue5392 x + ((2 : ℝ) * Sparse.eval nodeValue5394 x + ((2 : ℝ) * Sparse.eval nodeValue5395 x + ((1 : ℝ) * Sparse.eval nodeValue5396 x + ((1 : ℝ) * Sparse.eval nodeValue5469 x + 0))))))))))))))))))))

noncomputable def reducedSource2097 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4088 x + ((1 : ℝ) * Sparse.eval nodeValue4986 x + ((2 : ℝ) * Sparse.eval nodeValue4987 x + ((1 : ℝ) * Sparse.eval nodeValue5017 x + ((1 : ℝ) * Sparse.eval nodeValue5025 x + ((1 : ℝ) * Sparse.eval nodeValue5030 x + ((2 : ℝ) * Sparse.eval nodeValue5056 x + ((1 : ℝ) * Sparse.eval nodeValue5123 x + ((2 : ℝ) * Sparse.eval nodeValue5314 x + ((2 : ℝ) * Sparse.eval nodeValue5333 x + ((2 : ℝ) * Sparse.eval nodeValue5344 x + ((1 : ℝ) * Sparse.eval nodeValue5345 x + ((2 : ℝ) * Sparse.eval nodeValue5346 x + ((2 : ℝ) * Sparse.eval nodeValue5367 x + ((1 : ℝ) * Sparse.eval nodeValue5369 x + ((1 : ℝ) * Sparse.eval nodeValue5374 x + ((2 : ℝ) * Sparse.eval nodeValue5378 x + ((1 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5391 x + ((2 : ℝ) * Sparse.eval nodeValue5393 x + ((1 : ℝ) * Sparse.eval nodeValue5460 x + 0))))))))))))))))))))

noncomputable def reducedSource2098 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4073 x + ((2 : ℝ) * Sparse.eval nodeValue4074 x + ((4 : ℝ) * Sparse.eval nodeValue4075 x + ((1 : ℝ) * Sparse.eval nodeValue4078 x + ((2 : ℝ) * Sparse.eval nodeValue4080 x + ((2 : ℝ) * Sparse.eval nodeValue4082 x + ((2 : ℝ) * Sparse.eval nodeValue4086 x + ((1 : ℝ) * Sparse.eval nodeValue4087 x + ((4 : ℝ) * Sparse.eval nodeValue4088 x + ((2 : ℝ) * Sparse.eval nodeValue4089 x + ((2 : ℝ) * Sparse.eval nodeValue4090 x + ((2 : ℝ) * Sparse.eval nodeValue4091 x + ((4 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))))))))

noncomputable def reducedSource2099 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4672 x + ((1 : ℝ) * Sparse.eval nodeValue4685 x + ((1 : ℝ) * Sparse.eval nodeValue4859 x + ((1 : ℝ) * Sparse.eval nodeValue4967 x + ((3 : ℝ) * Sparse.eval nodeValue4969 x + ((1 : ℝ) * Sparse.eval nodeValue5166 x + ((3 : ℝ) * Sparse.eval nodeValue5374 x + ((1 : ℝ) * Sparse.eval nodeValue5383 x + ((6 : ℝ) * Sparse.eval nodeValue5384 x + ((3 : ℝ) * Sparse.eval nodeValue5387 x + ((1 : ℝ) * Sparse.eval nodeValue5437 x + ((3 : ℝ) * Sparse.eval nodeValue5439 x + ((3 : ℝ) * Sparse.eval nodeValue5448 x + 0))))))))))))

noncomputable def reducedSource2100 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4675 x + ((3 : ℝ) * Sparse.eval nodeValue4677 x + ((1 : ℝ) * Sparse.eval nodeValue4863 x + ((3 : ℝ) * Sparse.eval nodeValue4964 x + ((1 : ℝ) * Sparse.eval nodeValue4975 x + ((1 : ℝ) * Sparse.eval nodeValue5162 x + ((3 : ℝ) * Sparse.eval nodeValue5243 x + ((6 : ℝ) * Sparse.eval nodeValue5379 x + ((3 : ℝ) * Sparse.eval nodeValue5380 x + ((1 : ℝ) * Sparse.eval nodeValue5427 x + ((3 : ℝ) * Sparse.eval nodeValue5429 x + ((3 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5447 x + 0))))))))))))

noncomputable def reducedSource2101 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2139 x + ((3 : ℝ) * Sparse.eval nodeValue2142 x + ((1 : ℝ) * Sparse.eval nodeValue2232 x + ((1 : ℝ) * Sparse.eval nodeValue2690 x + ((3 : ℝ) * Sparse.eval nodeValue2697 x + ((3 : ℝ) * Sparse.eval nodeValue3554 x + ((1 : ℝ) * Sparse.eval nodeValue3563 x + ((6 : ℝ) * Sparse.eval nodeValue3832 x + ((3 : ℝ) * Sparse.eval nodeValue3836 x + ((1 : ℝ) * Sparse.eval nodeValue3844 x + ((3 : ℝ) * Sparse.eval nodeValue3846 x + ((3 : ℝ) * Sparse.eval nodeValue3875 x + ((1 : ℝ) * Sparse.eval nodeValue3909 x + 0))))))))))))

noncomputable def reducedSource2102 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4676 x + ((2 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4864 x + ((2 : ℝ) * Sparse.eval nodeValue4968 x + ((2 : ℝ) * Sparse.eval nodeValue4971 x + ((1 : ℝ) * Sparse.eval nodeValue5167 x + ((4 : ℝ) * Sparse.eval nodeValue5378 x + ((2 : ℝ) * Sparse.eval nodeValue5380 x + ((2 : ℝ) * Sparse.eval nodeValue5387 x + ((4 : ℝ) * Sparse.eval nodeValue5388 x + ((2 : ℝ) * Sparse.eval nodeValue5431 x + ((2 : ℝ) * Sparse.eval nodeValue5433 x + ((2 : ℝ) * Sparse.eval nodeValue5440 x + ((2 : ℝ) * Sparse.eval nodeValue5450 x + 0)))))))))))))

noncomputable def reducedSource2103 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4679 x + ((1 : ℝ) * Sparse.eval nodeValue4685 x + ((1 : ℝ) * Sparse.eval nodeValue4695 x + ((3 : ℝ) * Sparse.eval nodeValue4696 x + ((1 : ℝ) * Sparse.eval nodeValue4833 x + ((1 : ℝ) * Sparse.eval nodeValue4878 x + ((6 : ℝ) * Sparse.eval nodeValue5226 x + ((3 : ℝ) * Sparse.eval nodeValue5231 x + ((3 : ℝ) * Sparse.eval nodeValue5237 x + ((3 : ℝ) * Sparse.eval nodeValue5257 x + ((3 : ℝ) * Sparse.eval nodeValue5265 x + ((1 : ℝ) * Sparse.eval nodeValue5273 x + ((1 : ℝ) * Sparse.eval nodeValue5301 x + 0))))))))))))

noncomputable def reducedSource2104 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2150 x + ((1 : ℝ) * Sparse.eval nodeValue2156 x + ((1 : ℝ) * Sparse.eval nodeValue2204 x + ((1 : ℝ) * Sparse.eval nodeValue2231 x + ((1 : ℝ) * Sparse.eval nodeValue2234 x + ((3 : ℝ) * Sparse.eval nodeValue2238 x + ((6 : ℝ) * Sparse.eval nodeValue2669 x + ((3 : ℝ) * Sparse.eval nodeValue2676 x + ((3 : ℝ) * Sparse.eval nodeValue2684 x + ((3 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2741 x + ((3 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + 0))))))))))))

noncomputable def reducedSource2105 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue4939 x + ((4 : ℝ) * Sparse.eval nodeValue4941 x + ((2 : ℝ) * Sparse.eval nodeValue5167 x + ((4 : ℝ) * Sparse.eval nodeValue5393 x + ((2 : ℝ) * Sparse.eval nodeValue5418 x + ((2 : ℝ) * Sparse.eval nodeValue5460 x + ((4 : ℝ) * Sparse.eval nodeValue5465 x + ((4 : ℝ) * Sparse.eval nodeValue5482 x + ((4 : ℝ) * Sparse.eval nodeValue5486 x + 0))))))))

noncomputable def reducedSource2106 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4073 x + ((2 : ℝ) * Sparse.eval nodeValue4079 x + ((12 : ℝ) * Sparse.eval nodeValue4088 x + ((8 : ℝ) * Sparse.eval nodeValue4091 x + 0)))

noncomputable def reducedSource2107 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue5113 x + ((4 : ℝ) * Sparse.eval nodeValue5114 x + ((4 : ℝ) * Sparse.eval nodeValue5168 x + ((4 : ℝ) * Sparse.eval nodeValue5372 x + ((4 : ℝ) * Sparse.eval nodeValue5387 x + ((4 : ℝ) * Sparse.eval nodeValue5403 x + ((4 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5441 x + ((1 : ℝ) * Sparse.eval nodeValue5488 x + 0))))))))

noncomputable def reducedSource2108 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4759 x + ((4 : ℝ) * Sparse.eval nodeValue4763 x + ((4 : ℝ) * Sparse.eval nodeValue4801 x + ((4 : ℝ) * Sparse.eval nodeValue5335 x + ((4 : ℝ) * Sparse.eval nodeValue5351 x + ((4 : ℝ) * Sparse.eval nodeValue5416 x + ((4 : ℝ) * Sparse.eval nodeValue5423 x + ((4 : ℝ) * Sparse.eval nodeValue5433 x + ((1 : ℝ) * Sparse.eval nodeValue5497 x + 0))))))))

noncomputable def reducedSource2109 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4761 x + ((1 : ℝ) * Sparse.eval nodeValue4762 x + ((1 : ℝ) * Sparse.eval nodeValue4768 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((2 : ℝ) * Sparse.eval nodeValue5044 x + ((1 : ℝ) * Sparse.eval nodeValue5076 x + ((1 : ℝ) * Sparse.eval nodeValue5187 x + ((2 : ℝ) * Sparse.eval nodeValue5215 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((2 : ℝ) * Sparse.eval nodeValue5338 x + ((2 : ℝ) * Sparse.eval nodeValue5353 x + ((1 : ℝ) * Sparse.eval nodeValue5354 x + ((2 : ℝ) * Sparse.eval nodeValue5401 x + ((2 : ℝ) * Sparse.eval nodeValue5406 x + ((1 : ℝ) * Sparse.eval nodeValue5408 x + ((1 : ℝ) * Sparse.eval nodeValue5414 x + ((2 : ℝ) * Sparse.eval nodeValue5425 x + ((2 : ℝ) * Sparse.eval nodeValue5430 x + ((1 : ℝ) * Sparse.eval nodeValue5431 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + 0))))))))))))))))))))

noncomputable def reducedSource2110 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2171 x + ((1 : ℝ) * Sparse.eval nodeValue2175 x + ((1 : ℝ) * Sparse.eval nodeValue2178 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((2 : ℝ) * Sparse.eval nodeValue2653 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((2 : ℝ) * Sparse.eval nodeValue3474 x + ((1 : ℝ) * Sparse.eval nodeValue3477 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((2 : ℝ) * Sparse.eval nodeValue3755 x + ((2 : ℝ) * Sparse.eval nodeValue3761 x + ((1 : ℝ) * Sparse.eval nodeValue3769 x + ((2 : ℝ) * Sparse.eval nodeValue3804 x + ((1 : ℝ) * Sparse.eval nodeValue3806 x + ((2 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3849 x + ((1 : ℝ) * Sparse.eval nodeValue3869 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + 0))))))))))))))))))))

noncomputable def reducedSource2111 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4077 x + ((4 : ℝ) * Sparse.eval nodeValue4078 x + ((4 : ℝ) * Sparse.eval nodeValue4080 x + ((4 : ℝ) * Sparse.eval nodeValue4086 x + ((4 : ℝ) * Sparse.eval nodeValue4088 x + ((4 : ℝ) * Sparse.eval nodeValue4090 x + ((4 : ℝ) * Sparse.eval nodeValue4091 x + ((4 : ℝ) * Sparse.eval nodeValue4092 x + ((1 : ℝ) * Sparse.eval nodeValue4095 x + 0))))))))

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

noncomputable def reducedSource2113 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue686 x + ((1 : ℝ) * Sparse.eval nodeValue697 x + ((1 : ℝ) * Sparse.eval nodeValue1541 x + ((-1 : ℝ) * Sparse.eval nodeValue4062 x + 0)))

noncomputable def reducedSource2114 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1521 x + ((3 : ℝ) * Sparse.eval nodeValue1532 x + ((1 : ℝ) * Sparse.eval nodeValue1537 x + ((1 : ℝ) * Sparse.eval nodeValue1540 x + ((-1 : ℝ) * Sparse.eval nodeValue4060 x + 0))))

noncomputable def reducedSource2115 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1516 x + ((1 : ℝ) * Sparse.eval nodeValue1521 x + ((2 : ℝ) * Sparse.eval nodeValue1537 x + ((-1 : ℝ) * Sparse.eval nodeValue4060 x + 0)))

noncomputable def reducedSource2116 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue683 x + ((1 : ℝ) * Sparse.eval nodeValue691 x + ((1 : ℝ) * Sparse.eval nodeValue695 x + ((1 : ℝ) * Sparse.eval nodeValue1537 x + ((-1 : ℝ) * Sparse.eval nodeValue4060 x + 0))))

noncomputable def reducedSource2117 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1527 x + ((3 : ℝ) * Sparse.eval nodeValue1529 x + ((1 : ℝ) * Sparse.eval nodeValue1531 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0))))

noncomputable def reducedSource2118 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1523 x + ((1 : ℝ) * Sparse.eval nodeValue1527 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0))))

noncomputable def reducedSource2119 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1533 x + ((2 : ℝ) * Sparse.eval nodeValue1538 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0)))

noncomputable def reducedSource2120 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue696 x + ((3 : ℝ) * Sparse.eval nodeValue1496 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((1 : ℝ) * Sparse.eval nodeValue1539 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0))))

noncomputable def reducedSource2121 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue693 x + ((3 : ℝ) * Sparse.eval nodeValue1495 x + ((1 : ℝ) * Sparse.eval nodeValue1527 x + ((1 : ℝ) * Sparse.eval nodeValue1538 x + ((-1 : ℝ) * Sparse.eval nodeValue4061 x + 0))))

noncomputable def reducedSource2122 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1514 x + ((2 : ℝ) * Sparse.eval nodeValue1518 x + ((1 : ℝ) * Sparse.eval nodeValue1520 x + ((1 : ℝ) * Sparse.eval nodeValue1535 x + ((-1 : ℝ) * Sparse.eval nodeValue4058 x + 0))))

noncomputable def reducedSource2123 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1509 x + ((2 : ℝ) * Sparse.eval nodeValue1528 x + ((2 : ℝ) * Sparse.eval nodeValue1530 x + ((1 : ℝ) * Sparse.eval nodeValue1535 x + ((-1 : ℝ) * Sparse.eval nodeValue4058 x + 0))))

noncomputable def reducedSource2124 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1505 x + ((1 : ℝ) * Sparse.eval nodeValue1509 x + ((2 : ℝ) * Sparse.eval nodeValue1518 x + ((1 : ℝ) * Sparse.eval nodeValue1535 x + ((-1 : ℝ) * Sparse.eval nodeValue4058 x + 0))))

noncomputable def reducedSource2125 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1511 x + ((1 : ℝ) * Sparse.eval nodeValue1513 x + ((1 : ℝ) * Sparse.eval nodeValue1519 x + ((2 : ℝ) * Sparse.eval nodeValue1525 x + ((-1 : ℝ) * Sparse.eval nodeValue4059 x + 0))))

noncomputable def reducedSource2126 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1519 x + ((2 : ℝ) * Sparse.eval nodeValue1522 x + ((1 : ℝ) * Sparse.eval nodeValue1525 x + ((1 : ℝ) * Sparse.eval nodeValue1526 x + ((1 : ℝ) * Sparse.eval nodeValue1536 x + ((-1 : ℝ) * Sparse.eval nodeValue4059 x + 0)))))

noncomputable def reducedSource2127 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1515 x + ((2 : ℝ) * Sparse.eval nodeValue1519 x + ((2 : ℝ) * Sparse.eval nodeValue1536 x + ((-1 : ℝ) * Sparse.eval nodeValue4059 x + 0)))

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

noncomputable def reducedSource2128 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1501 x + ((1 : ℝ) * Sparse.eval nodeValue1503 x + ((3 : ℝ) * Sparse.eval nodeValue1507 x + ((1 : ℝ) * Sparse.eval nodeValue1524 x + ((-1 : ℝ) * Sparse.eval nodeValue4057 x + 0))))

noncomputable def reducedSource2129 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1504 x + ((1 : ℝ) * Sparse.eval nodeValue1507 x + ((1 : ℝ) * Sparse.eval nodeValue1508 x + ((3 : ℝ) * Sparse.eval nodeValue1517 x + ((-1 : ℝ) * Sparse.eval nodeValue4057 x + 0))))

noncomputable def reducedSource2130 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1507 x + ((1 : ℝ) * Sparse.eval nodeValue1510 x + ((2 : ℝ) * Sparse.eval nodeValue1512 x + ((1 : ℝ) * Sparse.eval nodeValue1517 x + ((1 : ℝ) * Sparse.eval nodeValue1524 x + ((-1 : ℝ) * Sparse.eval nodeValue4057 x + 0)))))

noncomputable def reducedSource2131 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue687 x + ((1 : ℝ) * Sparse.eval nodeValue1491 x + ((3 : ℝ) * Sparse.eval nodeValue1517 x + ((1 : ℝ) * Sparse.eval nodeValue1524 x + ((-1 : ℝ) * Sparse.eval nodeValue4057 x + 0))))

noncomputable def reducedSource2132 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1502 x + ((4 : ℝ) * Sparse.eval nodeValue1506 x + ((-1 : ℝ) * Sparse.eval nodeValue4056 x + 0))

noncomputable def reducedSource2133 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue666 x + ((1 : ℝ) * Sparse.eval nodeValue1497 x + ((4 : ℝ) * Sparse.eval nodeValue1506 x + ((-1 : ℝ) * Sparse.eval nodeValue4056 x + 0)))

noncomputable def reducedSource2134 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1688 x + ((2 : ℝ) * Sparse.eval nodeValue1692 x + ((2 : ℝ) * Sparse.eval nodeValue1695 x + ((-1 : ℝ) * Sparse.eval nodeValue4066 x + 0)))

noncomputable def reducedSource2135 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1692 x + ((2 : ℝ) * Sparse.eval nodeValue3262 x + ((2 : ℝ) * Sparse.eval nodeValue3275 x + ((-1 : ℝ) * Sparse.eval nodeValue4066 x + 0)))

noncomputable def reducedSource2136 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1685 x + ((1 : ℝ) * Sparse.eval nodeValue1687 x + ((1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue1743 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

noncomputable def reducedSource2137 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1679 x + ((1 : ℝ) * Sparse.eval nodeValue1683 x + ((1 : ℝ) * Sparse.eval nodeValue1693 x + ((1 : ℝ) * Sparse.eval nodeValue1735 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

noncomputable def reducedSource2138 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1689 x + ((1 : ℝ) * Sparse.eval nodeValue1693 x + ((1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue1748 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

noncomputable def reducedSource2139 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1683 x + ((2 : ℝ) * Sparse.eval nodeValue2149 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((1 : ℝ) * Sparse.eval nodeValue2258 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

noncomputable def reducedSource2140 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1694 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((2 : ℝ) * Sparse.eval nodeValue3268 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

noncomputable def reducedSource2141 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1693 x + ((2 : ℝ) * Sparse.eval nodeValue3272 x + ((2 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0))))

noncomputable def reducedSource2142 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1579 x + ((1 : ℝ) * Sparse.eval nodeValue3237 x + ((2 : ℝ) * Sparse.eval nodeValue3252 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((1 : ℝ) * Sparse.eval nodeValue3277 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

noncomputable def reducedSource2143 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1576 x + ((2 : ℝ) * Sparse.eval nodeValue1849 x + ((1 : ℝ) * Sparse.eval nodeValue1858 x + ((1 : ℝ) * Sparse.eval nodeValue2167 x + ((1 : ℝ) * Sparse.eval nodeValue3276 x + ((-1 : ℝ) * Sparse.eval nodeValue4067 x + 0)))))

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

noncomputable def reducedSource2144 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1690 x + ((1 : ℝ) * Sparse.eval nodeValue2184 x + ((1 : ℝ) * Sparse.eval nodeValue3255 x + ((2 : ℝ) * Sparse.eval nodeValue3264 x + ((1 : ℝ) * Sparse.eval nodeValue3273 x + ((-1 : ℝ) * Sparse.eval nodeValue4064 x + 0)))))

noncomputable def reducedSource2145 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1681 x + ((1 : ℝ) * Sparse.eval nodeValue2657 x + ((1 : ℝ) * Sparse.eval nodeValue3258 x + ((1 : ℝ) * Sparse.eval nodeValue3265 x + ((2 : ℝ) * Sparse.eval nodeValue3270 x + ((-1 : ℝ) * Sparse.eval nodeValue4065 x + 0)))))

noncomputable def reducedSource2146 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1691 x + ((1 : ℝ) * Sparse.eval nodeValue3261 x + ((2 : ℝ) * Sparse.eval nodeValue3265 x + ((2 : ℝ) * Sparse.eval nodeValue3274 x + ((-1 : ℝ) * Sparse.eval nodeValue4065 x + 0))))

noncomputable def reducedSource2147 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2161 x + ((2 : ℝ) * Sparse.eval nodeValue2163 x + ((2 : ℝ) * Sparse.eval nodeValue2169 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))

noncomputable def reducedSource2148 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2155 x + ((1 : ℝ) * Sparse.eval nodeValue2159 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2273 x + ((1 : ℝ) * Sparse.eval nodeValue3596 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))))

noncomputable def reducedSource2149 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2164 x + ((1 : ℝ) * Sparse.eval nodeValue2168 x + ((1 : ℝ) * Sparse.eval nodeValue2169 x + ((1 : ℝ) * Sparse.eval nodeValue2286 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))))

noncomputable def reducedSource2150 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2168 x + ((2 : ℝ) * Sparse.eval nodeValue3415 x + ((1 : ℝ) * Sparse.eval nodeValue3422 x + ((1 : ℝ) * Sparse.eval nodeValue3423 x + ((1 : ℝ) * Sparse.eval nodeValue3596 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))))

noncomputable def reducedSource2151 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3419 x + ((2 : ℝ) * Sparse.eval nodeValue3422 x + ((2 : ℝ) * Sparse.eval nodeValue3423 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))

noncomputable def reducedSource2152 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2169 x + ((2 : ℝ) * Sparse.eval nodeValue3423 x + ((2 : ℝ) * Sparse.eval nodeValue3512 x + ((-1 : ℝ) * Sparse.eval nodeValue4076 x + 0)))

noncomputable def reducedSource2153 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2147 x + ((1 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2153 x + ((1 : ℝ) * Sparse.eval nodeValue2165 x + ((1 : ℝ) * Sparse.eval nodeValue2256 x + ((1 : ℝ) * Sparse.eval nodeValue3457 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0))))))

noncomputable def reducedSource2154 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2160 x + ((2 : ℝ) * Sparse.eval nodeValue2162 x + ((1 : ℝ) * Sparse.eval nodeValue2165 x + ((1 : ℝ) * Sparse.eval nodeValue2180 x + ((1 : ℝ) * Sparse.eval nodeValue2186 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

noncomputable def reducedSource2155 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2140 x + ((1 : ℝ) * Sparse.eval nodeValue2143 x + ((2 : ℝ) * Sparse.eval nodeValue2151 x + ((1 : ℝ) * Sparse.eval nodeValue2239 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

noncomputable def reducedSource2156 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3408 x + ((2 : ℝ) * Sparse.eval nodeValue3411 x + ((1 : ℝ) * Sparse.eval nodeValue3413 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((1 : ℝ) * Sparse.eval nodeValue3457 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

noncomputable def reducedSource2157 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2181 x + ((1 : ℝ) * Sparse.eval nodeValue2185 x + ((1 : ℝ) * Sparse.eval nodeValue2186 x + ((2 : ℝ) * Sparse.eval nodeValue2223 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

noncomputable def reducedSource2158 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2185 x + ((1 : ℝ) * Sparse.eval nodeValue3403 x + ((2 : ℝ) * Sparse.eval nodeValue3411 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

noncomputable def reducedSource2159 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2143 x + ((1 : ℝ) * Sparse.eval nodeValue2176 x + ((1 : ℝ) * Sparse.eval nodeValue2185 x + ((2 : ℝ) * Sparse.eval nodeValue2212 x + ((1 : ℝ) * Sparse.eval nodeValue3588 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

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

noncomputable def reducedSource2160 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2165 x + ((1 : ℝ) * Sparse.eval nodeValue2186 x + ((1 : ℝ) * Sparse.eval nodeValue3420 x + ((2 : ℝ) * Sparse.eval nodeValue3457 x + ((1 : ℝ) * Sparse.eval nodeValue3510 x + ((-1 : ℝ) * Sparse.eval nodeValue4074 x + 0)))))

noncomputable def reducedSource2161 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2144 x + ((1 : ℝ) * Sparse.eval nodeValue2146 x + ((1 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2157 x + ((1 : ℝ) * Sparse.eval nodeValue2249 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((-1 : ℝ) * Sparse.eval nodeValue4075 x + 0))))))

noncomputable def reducedSource2162 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2154 x + ((1 : ℝ) * Sparse.eval nodeValue2157 x + ((1 : ℝ) * Sparse.eval nodeValue2158 x + ((1 : ℝ) * Sparse.eval nodeValue2166 x + ((1 : ℝ) * Sparse.eval nodeValue2272 x + ((1 : ℝ) * Sparse.eval nodeValue3595 x + ((-1 : ℝ) * Sparse.eval nodeValue4075 x + 0))))))

noncomputable def reducedSource2163 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2148 x + ((2 : ℝ) * Sparse.eval nodeValue2152 x + ((1 : ℝ) * Sparse.eval nodeValue2166 x + ((1 : ℝ) * Sparse.eval nodeValue2257 x + ((1 : ℝ) * Sparse.eval nodeValue3592 x + ((-1 : ℝ) * Sparse.eval nodeValue4075 x + 0)))))

noncomputable def reducedSource2164 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2658 x + ((1 : ℝ) * Sparse.eval nodeValue3406 x + ((1 : ℝ) * Sparse.eval nodeValue3412 x + ((2 : ℝ) * Sparse.eval nodeValue3417 x + ((1 : ℝ) * Sparse.eval nodeValue3591 x + ((-1 : ℝ) * Sparse.eval nodeValue4075 x + 0)))))

noncomputable def reducedSource2165 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2182 x + ((4 : ℝ) * Sparse.eval nodeValue3455 x + ((-1 : ℝ) * Sparse.eval nodeValue4077 x + 0))

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

noncomputable def reducedSource224 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource225 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1218 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2544 x + ((1 : ℝ) * Sparse.eval nodeValue2619 x + ((1 : ℝ) * Sparse.eval nodeValue2716 x + ((1 : ℝ) * Sparse.eval nodeValue2724 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource226 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1608 x + ((1 : ℝ) * Sparse.eval nodeValue1612 x + ((1 : ℝ) * Sparse.eval nodeValue1619 x + ((1 : ℝ) * Sparse.eval nodeValue1714 x + ((1 : ℝ) * Sparse.eval nodeValue2534 x + ((1 : ℝ) * Sparse.eval nodeValue2538 x + ((1 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3349 x + ((1 : ℝ) * Sparse.eval nodeValue3355 x + ((1 : ℝ) * Sparse.eval nodeValue3431 x + ((1 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3463 x + ((1 : ℝ) * Sparse.eval nodeValue3503 x + ((1 : ℝ) * Sparse.eval nodeValue3507 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3606 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((1 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3997 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource227 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue3983 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource228 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1392 x + ((1 : ℝ) * Sparse.eval nodeValue1394 x + ((1 : ℝ) * Sparse.eval nodeValue1400 x + ((1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue1425 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource229 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1406 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3097 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource230 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2624 x + ((1 : ℝ) * Sparse.eval nodeValue2949 x + ((1 : ℝ) * Sparse.eval nodeValue3013 x + ((1 : ℝ) * Sparse.eval nodeValue3014 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource231 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1392 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue3013 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3084 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource232 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2610 x + ((1 : ℝ) * Sparse.eval nodeValue2947 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue2992 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource233 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1425 x + ((1 : ℝ) * Sparse.eval nodeValue2992 x + ((1 : ℝ) * Sparse.eval nodeValue3014 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3108 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource234 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource235 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1400 x + ((1 : ℝ) * Sparse.eval nodeValue2942 x + ((1 : ℝ) * Sparse.eval nodeValue2947 x + ((1 : ℝ) * Sparse.eval nodeValue2949 x + ((1 : ℝ) * Sparse.eval nodeValue2964 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource236 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2496 x + ((1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2498 x + ((1 : ℝ) * Sparse.eval nodeValue2516 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue3028 x + ((1 : ℝ) * Sparse.eval nodeValue3035 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3042 x + ((1 : ℝ) * Sparse.eval nodeValue3063 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3067 x + ((1 : ℝ) * Sparse.eval nodeValue3080 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3211 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0))))))))))))))))))))))))))))

noncomputable def reducedSource237 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource238 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2033 x + ((1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource239 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3632 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

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

noncomputable def reducedSource240 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2973 x + ((1 : ℝ) * Sparse.eval nodeValue3490 x + ((1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource241 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2592 x + ((1 : ℝ) * Sparse.eval nodeValue3383 x + ((1 : ℝ) * Sparse.eval nodeValue3490 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource242 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3632 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource243 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource244 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1180 x + ((1 : ℝ) * Sparse.eval nodeValue1181 x + ((1 : ℝ) * Sparse.eval nodeValue1182 x + ((1 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1262 x + ((1 : ℝ) * Sparse.eval nodeValue2454 x + ((1 : ℝ) * Sparse.eval nodeValue2465 x + ((1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2834 x + ((1 : ℝ) * Sparse.eval nodeValue2835 x + ((1 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue2909 x + ((1 : ℝ) * Sparse.eval nodeValue2934 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue2998 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3883 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource245 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2836 x + ((1 : ℝ) * Sparse.eval nodeValue2837 x + ((1 : ℝ) * Sparse.eval nodeValue2838 x + ((1 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3241 x + ((1 : ℝ) * Sparse.eval nodeValue3242 x + ((1 : ℝ) * Sparse.eval nodeValue3243 x + ((1 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3294 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3461 x + ((1 : ℝ) * Sparse.eval nodeValue3471 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3515 x + ((1 : ℝ) * Sparse.eval nodeValue3518 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((1 : ℝ) * Sparse.eval nodeValue3559 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3809 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource246 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3906 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource247 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1222 x + ((1 : ℝ) * Sparse.eval nodeValue1224 x + ((1 : ℝ) * Sparse.eval nodeValue1226 x + ((1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue1277 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource248 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1277 x + ((1 : ℝ) * Sparse.eval nodeValue2577 x + ((1 : ℝ) * Sparse.eval nodeValue2650 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource249 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2495 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue3813 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource250 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1222 x + ((1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2645 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource251 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2547 x + ((1 : ℝ) * Sparse.eval nodeValue2549 x + ((1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue2577 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource252 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1237 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2739 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource253 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2645 x + ((1 : ℝ) * Sparse.eval nodeValue2647 x + ((1 : ℝ) * Sparse.eval nodeValue2649 x + ((1 : ℝ) * Sparse.eval nodeValue2650 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource254 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1226 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2549 x + ((1 : ℝ) * Sparse.eval nodeValue2649 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource255 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue988 x + ((1 : ℝ) * Sparse.eval nodeValue989 x + ((1 : ℝ) * Sparse.eval nodeValue993 x + ((1 : ℝ) * Sparse.eval nodeValue1001 x + ((1 : ℝ) * Sparse.eval nodeValue1057 x + ((1 : ℝ) * Sparse.eval nodeValue2390 x + ((1 : ℝ) * Sparse.eval nodeValue2391 x + ((1 : ℝ) * Sparse.eval nodeValue2395 x + ((1 : ℝ) * Sparse.eval nodeValue2401 x + ((1 : ℝ) * Sparse.eval nodeValue2453 x + ((1 : ℝ) * Sparse.eval nodeValue2456 x + ((1 : ℝ) * Sparse.eval nodeValue2460 x + ((1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2569 x + ((1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2621 x + ((1 : ℝ) * Sparse.eval nodeValue2637 x + ((1 : ℝ) * Sparse.eval nodeValue2664 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue2706 x + ((1 : ℝ) * Sparse.eval nodeValue2730 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2775 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3887 x + ((1 : ℝ) * Sparse.eval nodeValue3995 x + 0))))))))))))))))))))))))))))

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

noncomputable def reducedSource256 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((1 : ℝ) * Sparse.eval nodeValue3910 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource257 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1358 x + ((1 : ℝ) * Sparse.eval nodeValue1361 x + ((1 : ℝ) * Sparse.eval nodeValue1363 x + ((1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue1423 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource258 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1370 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3053 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource259 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2627 x + ((1 : ℝ) * Sparse.eval nodeValue2946 x + ((1 : ℝ) * Sparse.eval nodeValue3008 x + ((1 : ℝ) * Sparse.eval nodeValue3011 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3881 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource260 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1358 x + ((1 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue3008 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource261 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2625 x + ((1 : ℝ) * Sparse.eval nodeValue2918 x + ((1 : ℝ) * Sparse.eval nodeValue2972 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3880 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource262 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1423 x + ((1 : ℝ) * Sparse.eval nodeValue2625 x + ((1 : ℝ) * Sparse.eval nodeValue2627 x + ((1 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource263 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2862 x + ((1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3958 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource264 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1363 x + ((1 : ℝ) * Sparse.eval nodeValue2868 x + ((1 : ℝ) * Sparse.eval nodeValue2972 x + ((1 : ℝ) * Sparse.eval nodeValue3011 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource265 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2641 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3031 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3885 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource266 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1361 x + ((1 : ℝ) * Sparse.eval nodeValue2865 x + ((1 : ℝ) * Sparse.eval nodeValue2918 x + ((1 : ℝ) * Sparse.eval nodeValue2946 x + ((1 : ℝ) * Sparse.eval nodeValue3031 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource267 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4808 x + ((1 : ℝ) * Sparse.eval nodeValue4810 x + ((1 : ℝ) * Sparse.eval nodeValue4839 x + ((1 : ℝ) * Sparse.eval nodeValue4854 x + ((1 : ℝ) * Sparse.eval nodeValue4855 x + ((1 : ℝ) * Sparse.eval nodeValue4870 x + ((1 : ℝ) * Sparse.eval nodeValue4880 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((1 : ℝ) * Sparse.eval nodeValue5223 x + ((1 : ℝ) * Sparse.eval nodeValue5228 x + ((1 : ℝ) * Sparse.eval nodeValue5229 x + ((1 : ℝ) * Sparse.eval nodeValue5232 x + ((2 : ℝ) * Sparse.eval nodeValue5233 x + ((1 : ℝ) * Sparse.eval nodeValue5243 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((1 : ℝ) * Sparse.eval nodeValue5250 x + ((1 : ℝ) * Sparse.eval nodeValue5253 x + ((1 : ℝ) * Sparse.eval nodeValue5254 x + ((1 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5264 x + ((1 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5267 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + 0)))))))))))))))))))))))))))

noncomputable def reducedSource268 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2127 x + ((1 : ℝ) * Sparse.eval nodeValue2128 x + ((1 : ℝ) * Sparse.eval nodeValue2129 x + ((1 : ℝ) * Sparse.eval nodeValue2133 x + ((1 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2215 x + ((1 : ℝ) * Sparse.eval nodeValue2216 x + ((1 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2665 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2713 x + ((1 : ℝ) * Sparse.eval nodeValue2714 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3092 x + ((1 : ℝ) * Sparse.eval nodeValue3094 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource269 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2091 x + ((1 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2093 x + ((1 : ℝ) * Sparse.eval nodeValue2111 x + ((1 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2673 x + ((1 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3017 x + ((1 : ℝ) * Sparse.eval nodeValue3019 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3030 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3045 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3206 x + ((1 : ℝ) * Sparse.eval nodeValue3210 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource270 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource271 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

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

noncomputable def reducedSource272 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2266 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource273 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3159 x + ((1 : ℝ) * Sparse.eval nodeValue3377 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((2 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource274 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue3377 x + ((1 : ℝ) * Sparse.eval nodeValue3504 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource275 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3153 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3488 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource276 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue3153 x + ((1 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3157 x + ((1 : ℝ) * Sparse.eval nodeValue3159 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource277 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource278 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource279 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3157 x + ((1 : ℝ) * Sparse.eval nodeValue3392 x + ((1 : ℝ) * Sparse.eval nodeValue3504 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource280 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2028 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3488 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource281 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1178 x + ((1 : ℝ) * Sparse.eval nodeValue1179 x + ((1 : ℝ) * Sparse.eval nodeValue1182 x + ((1 : ℝ) * Sparse.eval nodeValue1185 x + ((1 : ℝ) * Sparse.eval nodeValue1261 x + ((1 : ℝ) * Sparse.eval nodeValue1992 x + ((1 : ℝ) * Sparse.eval nodeValue2004 x + ((1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2197 x + ((1 : ℝ) * Sparse.eval nodeValue2833 x + ((1 : ℝ) * Sparse.eval nodeValue2835 x + ((1 : ℝ) * Sparse.eval nodeValue2838 x + ((1 : ℝ) * Sparse.eval nodeValue2905 x + ((1 : ℝ) * Sparse.eval nodeValue2907 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue2979 x + ((1 : ℝ) * Sparse.eval nodeValue2997 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3025 x + ((1 : ℝ) * Sparse.eval nodeValue3037 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3109 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource282 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2001 x + ((1 : ℝ) * Sparse.eval nodeValue2004 x + ((1 : ℝ) * Sparse.eval nodeValue2005 x + ((1 : ℝ) * Sparse.eval nodeValue2055 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2833 x + ((1 : ℝ) * Sparse.eval nodeValue2835 x + ((1 : ℝ) * Sparse.eval nodeValue2838 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3238 x + ((1 : ℝ) * Sparse.eval nodeValue3240 x + ((1 : ℝ) * Sparse.eval nodeValue3243 x + ((1 : ℝ) * Sparse.eval nodeValue3296 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3479 x + ((1 : ℝ) * Sparse.eval nodeValue3480 x + ((1 : ℝ) * Sparse.eval nodeValue3517 x + ((1 : ℝ) * Sparse.eval nodeValue3518 x + ((1 : ℝ) * Sparse.eval nodeValue3526 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3534 x + ((1 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3561 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3577 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3856 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource283 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2732 x + ((2 : ℝ) * Sparse.eval nodeValue3814 x + ((1 : ℝ) * Sparse.eval nodeValue3841 x + ((1 : ℝ) * Sparse.eval nodeValue3906 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))

noncomputable def reducedSource284 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1278 x + ((1 : ℝ) * Sparse.eval nodeValue2578 x + ((1 : ℝ) * Sparse.eval nodeValue2649 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2758 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource285 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2499 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue3814 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource286 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue990 x + ((1 : ℝ) * Sparse.eval nodeValue991 x + ((1 : ℝ) * Sparse.eval nodeValue992 x + ((1 : ℝ) * Sparse.eval nodeValue1006 x + ((1 : ℝ) * Sparse.eval nodeValue1058 x + ((1 : ℝ) * Sparse.eval nodeValue2392 x + ((1 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2394 x + ((1 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2454 x + ((1 : ℝ) * Sparse.eval nodeValue2455 x + ((1 : ℝ) * Sparse.eval nodeValue2463 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue2618 x + ((1 : ℝ) * Sparse.eval nodeValue2620 x + ((1 : ℝ) * Sparse.eval nodeValue2638 x + ((1 : ℝ) * Sparse.eval nodeValue2728 x + ((1 : ℝ) * Sparse.eval nodeValue2729 x + ((1 : ℝ) * Sparse.eval nodeValue2732 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((1 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((1 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3876 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue4003 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource287 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1609 x + ((1 : ℝ) * Sparse.eval nodeValue1610 x + ((1 : ℝ) * Sparse.eval nodeValue1611 x + ((1 : ℝ) * Sparse.eval nodeValue1624 x + ((1 : ℝ) * Sparse.eval nodeValue1715 x + ((1 : ℝ) * Sparse.eval nodeValue2906 x + ((1 : ℝ) * Sparse.eval nodeValue2910 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3347 x + ((1 : ℝ) * Sparse.eval nodeValue3348 x + ((1 : ℝ) * Sparse.eval nodeValue3358 x + ((1 : ℝ) * Sparse.eval nodeValue3430 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3464 x + ((1 : ℝ) * Sparse.eval nodeValue3505 x + ((1 : ℝ) * Sparse.eval nodeValue3506 x + ((1 : ℝ) * Sparse.eval nodeValue3523 x + ((1 : ℝ) * Sparse.eval nodeValue3537 x + ((1 : ℝ) * Sparse.eval nodeValue3538 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((1 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3624 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3839 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3993 x + 0)))))))))))))))))))))))))))))

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

noncomputable def reducedSource288 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((1 : ℝ) * Sparse.eval nodeValue3857 x + ((1 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource289 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1357 x + ((1 : ℝ) * Sparse.eval nodeValue1359 x + ((1 : ℝ) * Sparse.eval nodeValue1362 x + ((1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue1422 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource290 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1367 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource291 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2579 x + ((1 : ℝ) * Sparse.eval nodeValue2582 x + ((1 : ℝ) * Sparse.eval nodeValue3007 x + ((1 : ℝ) * Sparse.eval nodeValue3010 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3854 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource292 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1357 x + ((1 : ℝ) * Sparse.eval nodeValue2861 x + ((1 : ℝ) * Sparse.eval nodeValue3007 x + ((1 : ℝ) * Sparse.eval nodeValue3036 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource293 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2547 x + ((1 : ℝ) * Sparse.eval nodeValue2580 x + ((1 : ℝ) * Sparse.eval nodeValue2971 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3840 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource294 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2558 x + ((1 : ℝ) * Sparse.eval nodeValue2861 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3845 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource295 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1362 x + ((1 : ℝ) * Sparse.eval nodeValue2867 x + ((1 : ℝ) * Sparse.eval nodeValue2971 x + ((1 : ℝ) * Sparse.eval nodeValue3010 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3040 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource296 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2036 x + ((1 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2038 x + ((1 : ℝ) * Sparse.eval nodeValue2059 x + ((1 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2670 x + ((1 : ℝ) * Sparse.eval nodeValue2672 x + ((1 : ℝ) * Sparse.eval nodeValue2677 x + ((1 : ℝ) * Sparse.eval nodeValue2722 x + ((1 : ℝ) * Sparse.eval nodeValue3015 x + ((1 : ℝ) * Sparse.eval nodeValue3016 x + ((1 : ℝ) * Sparse.eval nodeValue3018 x + ((1 : ℝ) * Sparse.eval nodeValue3028 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3035 x + ((1 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3042 x + ((1 : ℝ) * Sparse.eval nodeValue3044 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3086 x + ((1 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3198 x + ((1 : ℝ) * Sparse.eval nodeValue3210 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + 0)))))))))))))))))))))))))))))

noncomputable def reducedSource297 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2560 x + ((1 : ℝ) * Sparse.eval nodeValue3375 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((1 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource298 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2039 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource299 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3151 x + ((1 : ℝ) * Sparse.eval nodeValue3379 x + ((1 : ℝ) * Sparse.eval nodeValue3382 x + ((1 : ℝ) * Sparse.eval nodeValue3383 x + ((1 : ℝ) * Sparse.eval nodeValue3395 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource300 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2555 x + ((1 : ℝ) * Sparse.eval nodeValue3382 x + ((1 : ℝ) * Sparse.eval nodeValue3528 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3541 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource301 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3279 x + ((1 : ℝ) * Sparse.eval nodeValue3280 x + ((1 : ℝ) * Sparse.eval nodeValue3282 x + ((2 : ℝ) * Sparse.eval nodeValue3290 x + ((2 : ℝ) * Sparse.eval nodeValue3434 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3467 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3529 x + ((2 : ℝ) * Sparse.eval nodeValue3532 x + ((2 : ℝ) * Sparse.eval nodeValue3536 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((2 : ℝ) * Sparse.eval nodeValue3568 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3805 x + ((2 : ℝ) * Sparse.eval nodeValue3848 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + 0))))))))))))))))))))

noncomputable def reducedSource302 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((2 : ℝ) * Sparse.eval nodeValue3871 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource303 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1206 x + ((1 : ℝ) * Sparse.eval nodeValue1208 x + ((2 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue1247 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

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

noncomputable def reducedSource304 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1247 x + ((2 : ℝ) * Sparse.eval nodeValue2622 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource305 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2470 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue3800 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource306 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1213 x + ((1 : ℝ) * Sparse.eval nodeValue2480 x + ((1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((1 : ℝ) * Sparse.eval nodeValue2723 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource307 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2610 x + ((1 : ℝ) * Sparse.eval nodeValue2612 x + ((1 : ℝ) * Sparse.eval nodeValue2615 x + ((1 : ℝ) * Sparse.eval nodeValue2622 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue3871 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource308 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1208 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2612 x + ((1 : ℝ) * Sparse.eval nodeValue2709 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource309 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4801 x + ((2 : ℝ) * Sparse.eval nodeValue4803 x + ((1 : ℝ) * Sparse.eval nodeValue4831 x + ((1 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue5219 x + ((1 : ℝ) * Sparse.eval nodeValue5220 x + ((2 : ℝ) * Sparse.eval nodeValue5223 x + ((1 : ℝ) * Sparse.eval nodeValue5241 x + ((1 : ℝ) * Sparse.eval nodeValue5242 x + ((1 : ℝ) * Sparse.eval nodeValue5244 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5253 x + ((2 : ℝ) * Sparse.eval nodeValue5254 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((4 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5282 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + 0)))))))))))))))))))

noncomputable def reducedSource310 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2190 x + ((1 : ℝ) * Sparse.eval nodeValue2191 x + ((2 : ℝ) * Sparse.eval nodeValue2195 x + ((1 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2661 x + ((1 : ℝ) * Sparse.eval nodeValue2662 x + ((2 : ℝ) * Sparse.eval nodeValue2665 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2713 x + ((2 : ℝ) * Sparse.eval nodeValue2714 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((1 : ℝ) * Sparse.eval nodeValue2751 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue3029 x + ((1 : ℝ) * Sparse.eval nodeValue3080 x + ((1 : ℝ) * Sparse.eval nodeValue3081 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + 0))))))))))))))))))))

noncomputable def reducedSource311 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2695 x + ((1 : ℝ) * Sparse.eval nodeValue2698 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((2 : ℝ) * Sparse.eval nodeValue3017 x + ((2 : ℝ) * Sparse.eval nodeValue3019 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3066 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3069 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((1 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((2 : ℝ) * Sparse.eval nodeValue3202 x + ((1 : ℝ) * Sparse.eval nodeValue3205 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3227 x + 0))))))))))))))))))))

noncomputable def reducedSource312 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3493 x + ((1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource313 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2019 x + ((2 : ℝ) * Sparse.eval nodeValue2021 x + ((1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource314 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource315 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3375 x + ((2 : ℝ) * Sparse.eval nodeValue3377 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3497 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource316 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue3388 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((2 : ℝ) * Sparse.eval nodeValue3544 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource317 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3494 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((2 : ℝ) * Sparse.eval nodeValue3504 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((1 : ℝ) * Sparse.eval nodeValue3580 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource318 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2019 x + ((1 : ℝ) * Sparse.eval nodeValue3375 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource319 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1995 x + ((2 : ℝ) * Sparse.eval nodeValue1998 x + ((1 : ℝ) * Sparse.eval nodeValue2050 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue3278 x + ((1 : ℝ) * Sparse.eval nodeValue3280 x + ((2 : ℝ) * Sparse.eval nodeValue3288 x + ((1 : ℝ) * Sparse.eval nodeValue3476 x + ((2 : ℝ) * Sparse.eval nodeValue3477 x + ((1 : ℝ) * Sparse.eval nodeValue3531 x + ((2 : ℝ) * Sparse.eval nodeValue3532 x + ((2 : ℝ) * Sparse.eval nodeValue3536 x + ((2 : ℝ) * Sparse.eval nodeValue3537 x + ((2 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3574 x + ((1 : ℝ) * Sparse.eval nodeValue3576 x + ((1 : ℝ) * Sparse.eval nodeValue3812 x + ((2 : ℝ) * Sparse.eval nodeValue3840 x + ((1 : ℝ) * Sparse.eval nodeValue3851 x + ((1 : ℝ) * Sparse.eval nodeValue3855 x + 0))))))))))))))))))))

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

noncomputable def reducedSource32 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1067 x + ((2 : ℝ) * Sparse.eval nodeValue2041 x + ((1 : ℝ) * Sparse.eval nodeValue2284 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource33 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1459 x + ((2 : ℝ) * Sparse.eval nodeValue2041 x + ((2 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0))))

noncomputable def reducedSource34 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1069 x + ((3 : ℝ) * Sparse.eval nodeValue1459 x + ((1 : ℝ) * Sparse.eval nodeValue2285 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

noncomputable def reducedSource35 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue795 x + ((1 : ℝ) * Sparse.eval nodeValue797 x + ((1 : ℝ) * Sparse.eval nodeValue814 x + ((1 : ℝ) * Sparse.eval nodeValue829 x + ((2 : ℝ) * Sparse.eval nodeValue1355 x + ((1 : ℝ) * Sparse.eval nodeValue1369 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((2 : ℝ) * Sparse.eval nodeValue1903 x + ((2 : ℝ) * Sparse.eval nodeValue1916 x + ((2 : ℝ) * Sparse.eval nodeValue1927 x + ((2 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2063 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2113 x + ((2 : ℝ) * Sparse.eval nodeValue2254 x + ((1 : ℝ) * Sparse.eval nodeValue2267 x + ((1 : ℝ) * Sparse.eval nodeValue2280 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((2 : ℝ) * Sparse.eval nodeValue3222 x + ((1 : ℝ) * Sparse.eval nodeValue3224 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0))))))))))))))))))))

noncomputable def reducedSource36 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((2 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource37 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1029 x + ((1 : ℝ) * Sparse.eval nodeValue1031 x + ((1 : ℝ) * Sparse.eval nodeValue1047 x + ((1 : ℝ) * Sparse.eval nodeValue1061 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource38 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1029 x + ((1 : ℝ) * Sparse.eval nodeValue2013 x + ((1 : ℝ) * Sparse.eval nodeValue2096 x + ((1 : ℝ) * Sparse.eval nodeValue2125 x + ((1 : ℝ) * Sparse.eval nodeValue2253 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource39 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1458 x + ((1 : ℝ) * Sparse.eval nodeValue2013 x + ((1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue3156 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

noncomputable def reducedSource40 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1061 x + ((2 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2136 x + ((1 : ℝ) * Sparse.eval nodeValue2255 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

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

noncomputable def reducedSource320 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((2 : ℝ) * Sparse.eval nodeValue3872 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((1 : ℝ) * Sparse.eval nodeValue3901 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource321 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1248 x + ((2 : ℝ) * Sparse.eval nodeValue2623 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2745 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource322 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2473 x + ((2 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue3801 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource323 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1216 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((2 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource324 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2611 x + ((1 : ℝ) * Sparse.eval nodeValue2612 x + ((1 : ℝ) * Sparse.eval nodeValue2617 x + ((1 : ℝ) * Sparse.eval nodeValue2623 x + ((1 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue3872 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource325 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2707 x + ((3 : ℝ) * Sparse.eval nodeValue2710 x + ((1 : ℝ) * Sparse.eval nodeValue2745 x + ((1 : ℝ) * Sparse.eval nodeValue3899 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))

noncomputable def reducedSource326 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4391 x + ((1 : ℝ) * Sparse.eval nodeValue4392 x + ((2 : ℝ) * Sparse.eval nodeValue4400 x + ((1 : ℝ) * Sparse.eval nodeValue4439 x + ((1 : ℝ) * Sparse.eval nodeValue4992 x + ((1 : ℝ) * Sparse.eval nodeValue4993 x + ((2 : ℝ) * Sparse.eval nodeValue4999 x + ((2 : ℝ) * Sparse.eval nodeValue5128 x + ((2 : ℝ) * Sparse.eval nodeValue5129 x + ((2 : ℝ) * Sparse.eval nodeValue5138 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((1 : ℝ) * Sparse.eval nodeValue5249 x + ((1 : ℝ) * Sparse.eval nodeValue5252 x + ((2 : ℝ) * Sparse.eval nodeValue5255 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((1 : ℝ) * Sparse.eval nodeValue5281 x + ((1 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5424 x + ((1 : ℝ) * Sparse.eval nodeValue5429 x + ((1 : ℝ) * Sparse.eval nodeValue5439 x + ((1 : ℝ) * Sparse.eval nodeValue5481 x + 0))))))))))))))))))))

noncomputable def reducedSource327 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue972 x + ((1 : ℝ) * Sparse.eval nodeValue973 x + ((2 : ℝ) * Sparse.eval nodeValue981 x + ((1 : ℝ) * Sparse.eval nodeValue1021 x + ((1 : ℝ) * Sparse.eval nodeValue2378 x + ((1 : ℝ) * Sparse.eval nodeValue2379 x + ((2 : ℝ) * Sparse.eval nodeValue2384 x + ((2 : ℝ) * Sparse.eval nodeValue2543 x + ((2 : ℝ) * Sparse.eval nodeValue2545 x + ((2 : ℝ) * Sparse.eval nodeValue2557 x + ((2 : ℝ) * Sparse.eval nodeValue2570 x + ((1 : ℝ) * Sparse.eval nodeValue2708 x + ((1 : ℝ) * Sparse.eval nodeValue2712 x + ((2 : ℝ) * Sparse.eval nodeValue2718 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((1 : ℝ) * Sparse.eval nodeValue2750 x + ((1 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue3954 x + ((1 : ℝ) * Sparse.eval nodeValue3979 x + ((2 : ℝ) * Sparse.eval nodeValue3990 x + ((1 : ℝ) * Sparse.eval nodeValue4012 x + 0))))))))))))))))))))

noncomputable def reducedSource328 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1606 x + ((2 : ℝ) * Sparse.eval nodeValue1607 x + ((1 : ℝ) * Sparse.eval nodeValue1613 x + ((1 : ℝ) * Sparse.eval nodeValue1713 x + ((1 : ℝ) * Sparse.eval nodeValue3345 x + ((2 : ℝ) * Sparse.eval nodeValue3346 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((1 : ℝ) * Sparse.eval nodeValue3502 x + ((2 : ℝ) * Sparse.eval nodeValue3503 x + ((2 : ℝ) * Sparse.eval nodeValue3516 x + ((2 : ℝ) * Sparse.eval nodeValue3517 x + ((2 : ℝ) * Sparse.eval nodeValue3519 x + ((2 : ℝ) * Sparse.eval nodeValue3540 x + ((1 : ℝ) * Sparse.eval nodeValue3543 x + ((1 : ℝ) * Sparse.eval nodeValue3571 x + ((2 : ℝ) * Sparse.eval nodeValue3605 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3843 x + ((1 : ℝ) * Sparse.eval nodeValue3858 x + ((1 : ℝ) * Sparse.eval nodeValue3874 x + ((1 : ℝ) * Sparse.eval nodeValue3991 x + 0))))))))))))))))))))

noncomputable def reducedSource329 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3064 x + ((2 : ℝ) * Sparse.eval nodeValue3838 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((1 : ℝ) * Sparse.eval nodeValue3902 x + ((1 : ℝ) * Sparse.eval nodeValue4008 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource330 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1378 x + ((1 : ℝ) * Sparse.eval nodeValue1380 x + ((1 : ℝ) * Sparse.eval nodeValue1383 x + ((2 : ℝ) * Sparse.eval nodeValue1392 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource331 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1383 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3074 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource332 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2562 x + ((1 : ℝ) * Sparse.eval nodeValue3012 x + ((2 : ℝ) * Sparse.eval nodeValue3013 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3846 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource333 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2543 x + ((1 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3838 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

noncomputable def reducedSource334 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1380 x + ((2 : ℝ) * Sparse.eval nodeValue2916 x + ((1 : ℝ) * Sparse.eval nodeValue3012 x + ((1 : ℝ) * Sparse.eval nodeValue3064 x + ((1 : ℝ) * Sparse.eval nodeValue3066 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

noncomputable def reducedSource335 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2693 x + ((1 : ℝ) * Sparse.eval nodeValue2694 x + ((1 : ℝ) * Sparse.eval nodeValue2697 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue3015 x + ((2 : ℝ) * Sparse.eval nodeValue3016 x + ((2 : ℝ) * Sparse.eval nodeValue3018 x + ((2 : ℝ) * Sparse.eval nodeValue3038 x + ((1 : ℝ) * Sparse.eval nodeValue3063 x + ((1 : ℝ) * Sparse.eval nodeValue3065 x + ((1 : ℝ) * Sparse.eval nodeValue3067 x + ((1 : ℝ) * Sparse.eval nodeValue3068 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3196 x + ((1 : ℝ) * Sparse.eval nodeValue3197 x + ((1 : ℝ) * Sparse.eval nodeValue3209 x + ((1 : ℝ) * Sparse.eval nodeValue3223 x + 0))))))))))))))))))))

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

noncomputable def reducedSource336 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2552 x + ((1 : ℝ) * Sparse.eval nodeValue3488 x + ((1 : ℝ) * Sparse.eval nodeValue3493 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource337 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2033 x + ((2 : ℝ) * Sparse.eval nodeValue2034 x + ((1 : ℝ) * Sparse.eval nodeValue2051 x + ((1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource338 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2277 x + ((1 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue3539 x + ((1 : ℝ) * Sparse.eval nodeValue3625 x + ((2 : ℝ) * Sparse.eval nodeValue3632 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource339 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4619 x + ((1 : ℝ) * Sparse.eval nodeValue4621 x + ((1 : ℝ) * Sparse.eval nodeValue4627 x + ((3 : ℝ) * Sparse.eval nodeValue4871 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((6 : ℝ) * Sparse.eval nodeValue5170 x + ((3 : ℝ) * Sparse.eval nodeValue5176 x + ((3 : ℝ) * Sparse.eval nodeValue5302 x + ((3 : ℝ) * Sparse.eval nodeValue5306 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((3 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5456 x + 0))))))))))))

noncomputable def reducedSource340 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1294 x + ((1 : ℝ) * Sparse.eval nodeValue1297 x + ((1 : ℝ) * Sparse.eval nodeValue1311 x + ((3 : ℝ) * Sparse.eval nodeValue2112 x + ((1 : ℝ) * Sparse.eval nodeValue2281 x + ((6 : ℝ) * Sparse.eval nodeValue2954 x + ((3 : ℝ) * Sparse.eval nodeValue2968 x + ((3 : ℝ) * Sparse.eval nodeValue3054 x + ((3 : ℝ) * Sparse.eval nodeValue3120 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((3 : ℝ) * Sparse.eval nodeValue3889 x + ((1 : ℝ) * Sparse.eval nodeValue3916 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + 0))))))))))))

noncomputable def reducedSource341 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4503 x + ((1 : ℝ) * Sparse.eval nodeValue4507 x + ((1 : ℝ) * Sparse.eval nodeValue4510 x + ((6 : ℝ) * Sparse.eval nodeValue5105 x + ((3 : ℝ) * Sparse.eval nodeValue5109 x + ((3 : ℝ) * Sparse.eval nodeValue5110 x + ((3 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((3 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((3 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5494 x + 0))))))))))))

noncomputable def reducedSource342 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1087 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((1 : ℝ) * Sparse.eval nodeValue1094 x + ((6 : ℝ) * Sparse.eval nodeValue2515 x + ((3 : ℝ) * Sparse.eval nodeValue2519 x + ((3 : ℝ) * Sparse.eval nodeValue2522 x + ((3 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((3 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((3 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4020 x + 0))))))))))))

noncomputable def reducedSource343 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4899 x + ((1 : ℝ) * Sparse.eval nodeValue4901 x + ((6 : ℝ) * Sparse.eval nodeValue5260 x + ((3 : ℝ) * Sparse.eval nodeValue5275 x + ((3 : ℝ) * Sparse.eval nodeValue5276 x + ((3 : ℝ) * Sparse.eval nodeValue5291 x + ((3 : ℝ) * Sparse.eval nodeValue5294 x + ((3 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5305 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5311 x + 0))))))))))))

noncomputable def reducedSource344 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2293 x + ((1 : ℝ) * Sparse.eval nodeValue2294 x + ((6 : ℝ) * Sparse.eval nodeValue2724 x + ((3 : ℝ) * Sparse.eval nodeValue2743 x + ((3 : ℝ) * Sparse.eval nodeValue2744 x + ((3 : ℝ) * Sparse.eval nodeValue2768 x + ((3 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((3 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3125 x + 0))))))))))))

noncomputable def reducedSource345 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue2765 x + ((3 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((6 : ℝ) * Sparse.eval nodeValue3086 x + ((3 : ℝ) * Sparse.eval nodeValue3098 x + ((3 : ℝ) * Sparse.eval nodeValue3101 x + ((3 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((3 : ℝ) * Sparse.eval nodeValue3225 x + ((1 : ℝ) * Sparse.eval nodeValue3231 x + 0))))))))))))

noncomputable def reducedSource346 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2783 x + ((3 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3629 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource347 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3629 x + ((3 : ℝ) * Sparse.eval nodeValue3632 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((1 : ℝ) * Sparse.eval nodeValue3635 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource348 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2293 x + ((3 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3633 x + ((1 : ℝ) * Sparse.eval nodeValue3635 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource349 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1088 x + ((1 : ℝ) * Sparse.eval nodeValue1092 x + ((1 : ℝ) * Sparse.eval nodeValue1093 x + ((6 : ℝ) * Sparse.eval nodeValue2516 x + ((3 : ℝ) * Sparse.eval nodeValue2520 x + ((3 : ℝ) * Sparse.eval nodeValue2521 x + ((3 : ℝ) * Sparse.eval nodeValue2761 x + ((3 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2778 x + ((1 : ℝ) * Sparse.eval nodeValue2780 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((3 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + 0))))))))))))

noncomputable def reducedSource350 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1303 x + ((1 : ℝ) * Sparse.eval nodeValue1309 x + ((1 : ℝ) * Sparse.eval nodeValue1310 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource351 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1303 x + ((1 : ℝ) * Sparse.eval nodeValue2134 x + ((2 : ℝ) * Sparse.eval nodeValue2597 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

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

noncomputable def reducedSource352 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1310 x + ((3 : ℝ) * Sparse.eval nodeValue2603 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

noncomputable def reducedSource353 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4606 x + ((1 : ℝ) * Sparse.eval nodeValue4608 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4624 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((1 : ℝ) * Sparse.eval nodeValue5109 x + ((2 : ℝ) * Sparse.eval nodeValue5148 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((2 : ℝ) * Sparse.eval nodeValue5203 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5451 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + 0))))))))))))))))))))

noncomputable def reducedSource354 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1240 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1301 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((1 : ℝ) * Sparse.eval nodeValue2519 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((2 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2927 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((2 : ℝ) * Sparse.eval nodeValue2960 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))

noncomputable def reducedSource355 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4458 x + ((1 : ℝ) * Sparse.eval nodeValue4460 x + ((1 : ℝ) * Sparse.eval nodeValue4467 x + ((1 : ℝ) * Sparse.eval nodeValue4499 x + ((2 : ℝ) * Sparse.eval nodeValue5073 x + ((2 : ℝ) * Sparse.eval nodeValue5075 x + ((2 : ℝ) * Sparse.eval nodeValue5081 x + ((2 : ℝ) * Sparse.eval nodeValue5102 x + ((2 : ℝ) * Sparse.eval nodeValue5169 x + ((1 : ℝ) * Sparse.eval nodeValue5171 x + ((1 : ℝ) * Sparse.eval nodeValue5177 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((1 : ℝ) * Sparse.eval nodeValue5261 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5306 x + ((2 : ℝ) * Sparse.eval nodeValue5483 x + ((1 : ℝ) * Sparse.eval nodeValue5487 x + ((1 : ℝ) * Sparse.eval nodeValue5491 x + ((1 : ℝ) * Sparse.eval nodeValue5493 x + 0))))))))))))))))))))

noncomputable def reducedSource356 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1041 x + ((1 : ℝ) * Sparse.eval nodeValue1043 x + ((1 : ℝ) * Sparse.eval nodeValue1050 x + ((1 : ℝ) * Sparse.eval nodeValue1083 x + ((2 : ℝ) * Sparse.eval nodeValue2480 x + ((2 : ℝ) * Sparse.eval nodeValue2482 x + ((2 : ℝ) * Sparse.eval nodeValue2489 x + ((2 : ℝ) * Sparse.eval nodeValue2512 x + ((2 : ℝ) * Sparse.eval nodeValue2595 x + ((1 : ℝ) * Sparse.eval nodeValue2598 x + ((1 : ℝ) * Sparse.eval nodeValue2605 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2726 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((2 : ℝ) * Sparse.eval nodeValue2766 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((2 : ℝ) * Sparse.eval nodeValue3981 x + ((1 : ℝ) * Sparse.eval nodeValue4000 x + ((1 : ℝ) * Sparse.eval nodeValue4014 x + ((1 : ℝ) * Sparse.eval nodeValue4018 x + 0))))))))))))))))))))

noncomputable def reducedSource357 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4888 x + ((1 : ℝ) * Sparse.eval nodeValue4894 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((2 : ℝ) * Sparse.eval nodeValue5250 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((4 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5266 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5275 x + ((2 : ℝ) * Sparse.eval nodeValue5282 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5300 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((2 : ℝ) * Sparse.eval nodeValue5309 x + 0))))))))))))))))))

noncomputable def reducedSource358 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2244 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((2 : ℝ) * Sparse.eval nodeValue2709 x + ((2 : ℝ) * Sparse.eval nodeValue2722 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2731 x + ((2 : ℝ) * Sparse.eval nodeValue2751 x + ((2 : ℝ) * Sparse.eval nodeValue2753 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue2767 x + ((1 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2786 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + 0))))))))))))))))))))

noncomputable def reducedSource359 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2723 x + ((1 : ℝ) * Sparse.eval nodeValue2742 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3065 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3078 x + ((2 : ℝ) * Sparse.eval nodeValue3088 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((2 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3123 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + ((2 : ℝ) * Sparse.eval nodeValue3227 x + ((1 : ℝ) * Sparse.eval nodeValue3229 x + ((1 : ℝ) * Sparse.eval nodeValue3230 x + 0))))))))))))))))))))

noncomputable def reducedSource360 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue3544 x + ((1 : ℝ) * Sparse.eval nodeValue3547 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((1 : ℝ) * Sparse.eval nodeValue3635 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource361 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2262 x + ((1 : ℝ) * Sparse.eval nodeValue2264 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2291 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource362 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue3627 x + ((1 : ℝ) * Sparse.eval nodeValue3629 x + ((2 : ℝ) * Sparse.eval nodeValue3635 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))

noncomputable def reducedSource363 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3548 x + ((2 : ℝ) * Sparse.eval nodeValue3580 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource364 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2264 x + ((2 : ℝ) * Sparse.eval nodeValue3533 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3627 x + ((1 : ℝ) * Sparse.eval nodeValue3629 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource365 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4602 x + ((1 : ℝ) * Sparse.eval nodeValue4605 x + ((1 : ℝ) * Sparse.eval nodeValue4612 x + ((1 : ℝ) * Sparse.eval nodeValue4623 x + ((2 : ℝ) * Sparse.eval nodeValue4807 x + ((1 : ℝ) * Sparse.eval nodeValue4843 x + ((1 : ℝ) * Sparse.eval nodeValue4890 x + ((2 : ℝ) * Sparse.eval nodeValue5149 x + ((2 : ℝ) * Sparse.eval nodeValue5152 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((2 : ℝ) * Sparse.eval nodeValue5204 x + ((1 : ℝ) * Sparse.eval nodeValue5207 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((2 : ℝ) * Sparse.eval nodeValue5292 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((1 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5307 x + ((2 : ℝ) * Sparse.eval nodeValue5435 x + ((1 : ℝ) * Sparse.eval nodeValue5443 x + ((1 : ℝ) * Sparse.eval nodeValue5453 x + ((1 : ℝ) * Sparse.eval nodeValue5454 x + 0))))))))))))))))))))

noncomputable def reducedSource366 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1236 x + ((1 : ℝ) * Sparse.eval nodeValue1239 x + ((1 : ℝ) * Sparse.eval nodeValue1246 x + ((1 : ℝ) * Sparse.eval nodeValue1300 x + ((2 : ℝ) * Sparse.eval nodeValue2025 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((1 : ℝ) * Sparse.eval nodeValue2247 x + ((2 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2889 x + ((2 : ℝ) * Sparse.eval nodeValue2924 x + ((2 : ℝ) * Sparse.eval nodeValue2931 x + ((2 : ℝ) * Sparse.eval nodeValue2959 x + ((2 : ℝ) * Sparse.eval nodeValue3077 x + ((2 : ℝ) * Sparse.eval nodeValue3100 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3102 x + ((1 : ℝ) * Sparse.eval nodeValue3122 x + ((2 : ℝ) * Sparse.eval nodeValue3853 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((1 : ℝ) * Sparse.eval nodeValue3912 x + ((1 : ℝ) * Sparse.eval nodeValue4040 x + 0))))))))))))))))))))

noncomputable def reducedSource367 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4461 x + ((1 : ℝ) * Sparse.eval nodeValue4463 x + ((1 : ℝ) * Sparse.eval nodeValue4466 x + ((1 : ℝ) * Sparse.eval nodeValue4503 x + ((2 : ℝ) * Sparse.eval nodeValue5076 x + ((2 : ℝ) * Sparse.eval nodeValue5078 x + ((2 : ℝ) * Sparse.eval nodeValue5080 x + ((2 : ℝ) * Sparse.eval nodeValue5105 x + ((2 : ℝ) * Sparse.eval nodeValue5172 x + ((1 : ℝ) * Sparse.eval nodeValue5174 x + ((1 : ℝ) * Sparse.eval nodeValue5176 x + ((2 : ℝ) * Sparse.eval nodeValue5290 x + ((1 : ℝ) * Sparse.eval nodeValue5291 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5296 x + ((1 : ℝ) * Sparse.eval nodeValue5304 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + ((2 : ℝ) * Sparse.eval nodeValue5434 x + ((1 : ℝ) * Sparse.eval nodeValue5442 x + ((1 : ℝ) * Sparse.eval nodeValue5455 x + ((1 : ℝ) * Sparse.eval nodeValue5492 x + 0))))))))))))))))))))

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

noncomputable def reducedSource368 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1044 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((1 : ℝ) * Sparse.eval nodeValue1049 x + ((1 : ℝ) * Sparse.eval nodeValue1087 x + ((2 : ℝ) * Sparse.eval nodeValue2483 x + ((2 : ℝ) * Sparse.eval nodeValue2485 x + ((2 : ℝ) * Sparse.eval nodeValue2488 x + ((2 : ℝ) * Sparse.eval nodeValue2515 x + ((2 : ℝ) * Sparse.eval nodeValue2599 x + ((1 : ℝ) * Sparse.eval nodeValue2601 x + ((1 : ℝ) * Sparse.eval nodeValue2604 x + ((2 : ℝ) * Sparse.eval nodeValue2764 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2770 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((2 : ℝ) * Sparse.eval nodeValue3982 x + ((1 : ℝ) * Sparse.eval nodeValue4001 x + ((1 : ℝ) * Sparse.eval nodeValue4017 x + ((1 : ℝ) * Sparse.eval nodeValue4019 x + 0))))))))))))))))))))

noncomputable def reducedSource369 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue4889 x + ((1 : ℝ) * Sparse.eval nodeValue4895 x + ((1 : ℝ) * Sparse.eval nodeValue4896 x + ((1 : ℝ) * Sparse.eval nodeValue4898 x + ((2 : ℝ) * Sparse.eval nodeValue5251 x + ((2 : ℝ) * Sparse.eval nodeValue5258 x + ((2 : ℝ) * Sparse.eval nodeValue5259 x + ((2 : ℝ) * Sparse.eval nodeValue5260 x + ((2 : ℝ) * Sparse.eval nodeValue5267 x + ((2 : ℝ) * Sparse.eval nodeValue5270 x + ((1 : ℝ) * Sparse.eval nodeValue5272 x + ((1 : ℝ) * Sparse.eval nodeValue5274 x + ((1 : ℝ) * Sparse.eval nodeValue5276 x + ((2 : ℝ) * Sparse.eval nodeValue5284 x + ((1 : ℝ) * Sparse.eval nodeValue5293 x + ((2 : ℝ) * Sparse.eval nodeValue5294 x + ((1 : ℝ) * Sparse.eval nodeValue5295 x + ((1 : ℝ) * Sparse.eval nodeValue5302 x + ((1 : ℝ) * Sparse.eval nodeValue5308 x + ((1 : ℝ) * Sparse.eval nodeValue5309 x + ((1 : ℝ) * Sparse.eval nodeValue5310 x + 0))))))))))))))))))))

noncomputable def reducedSource370 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2245 x + ((1 : ℝ) * Sparse.eval nodeValue2265 x + ((1 : ℝ) * Sparse.eval nodeValue2266 x + ((1 : ℝ) * Sparse.eval nodeValue2279 x + ((2 : ℝ) * Sparse.eval nodeValue2710 x + ((2 : ℝ) * Sparse.eval nodeValue2723 x + ((2 : ℝ) * Sparse.eval nodeValue2724 x + ((2 : ℝ) * Sparse.eval nodeValue2732 x + ((2 : ℝ) * Sparse.eval nodeValue2753 x + ((2 : ℝ) * Sparse.eval nodeValue2754 x + ((1 : ℝ) * Sparse.eval nodeValue2767 x + ((2 : ℝ) * Sparse.eval nodeValue2768 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2777 x + ((1 : ℝ) * Sparse.eval nodeValue2787 x + ((1 : ℝ) * Sparse.eval nodeValue2788 x + ((2 : ℝ) * Sparse.eval nodeValue3089 x + ((1 : ℝ) * Sparse.eval nodeValue3112 x + ((1 : ℝ) * Sparse.eval nodeValue3113 x + ((1 : ℝ) * Sparse.eval nodeValue3124 x + 0))))))))))))))))))))

noncomputable def reducedSource371 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1229 x + ((1 : ℝ) * Sparse.eval nodeValue1231 x + ((1 : ℝ) * Sparse.eval nodeValue1245 x + ((1 : ℝ) * Sparse.eval nodeValue1292 x + ((2 : ℝ) * Sparse.eval nodeValue1639 x + ((1 : ℝ) * Sparse.eval nodeValue1651 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((2 : ℝ) * Sparse.eval nodeValue2875 x + ((1 : ℝ) * Sparse.eval nodeValue2888 x + ((2 : ℝ) * Sparse.eval nodeValue2921 x + ((2 : ℝ) * Sparse.eval nodeValue2930 x + ((2 : ℝ) * Sparse.eval nodeValue2952 x + ((2 : ℝ) * Sparse.eval nodeValue3024 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3097 x + ((1 : ℝ) * Sparse.eval nodeValue3103 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3626 x + ((1 : ℝ) * Sparse.eval nodeValue3987 x + 0))))))))))))))))))))

noncomputable def reducedSource372 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1070 x + ((1 : ℝ) * Sparse.eval nodeValue1072 x + ((1 : ℝ) * Sparse.eval nodeValue1076 x + ((1 : ℝ) * Sparse.eval nodeValue1084 x + ((2 : ℝ) * Sparse.eval nodeValue2500 x + ((2 : ℝ) * Sparse.eval nodeValue2502 x + ((2 : ℝ) * Sparse.eval nodeValue2506 x + ((2 : ℝ) * Sparse.eval nodeValue2513 x + ((2 : ℝ) * Sparse.eval nodeValue2681 x + ((1 : ℝ) * Sparse.eval nodeValue2683 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((1 : ℝ) * Sparse.eval nodeValue3582 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + 0))))))))))))))))))))

noncomputable def reducedSource373 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2769 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3054 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource374 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1268 x + ((1 : ℝ) * Sparse.eval nodeValue1272 x + ((1 : ℝ) * Sparse.eval nodeValue1273 x + ((1 : ℝ) * Sparse.eval nodeValue1306 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource375 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1268 x + ((1 : ℝ) * Sparse.eval nodeValue2571 x + ((1 : ℝ) * Sparse.eval nodeValue2639 x + ((1 : ℝ) * Sparse.eval nodeValue2759 x + ((1 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource376 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1433 x + ((1 : ℝ) * Sparse.eval nodeValue2571 x + ((1 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2600 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue3051 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

noncomputable def reducedSource377 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1437 x + ((2 : ℝ) * Sparse.eval nodeValue2639 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource378 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1273 x + ((2 : ℝ) * Sparse.eval nodeValue2575 x + ((1 : ℝ) * Sparse.eval nodeValue2643 x + ((1 : ℝ) * Sparse.eval nodeValue2765 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource379 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1272 x + ((2 : ℝ) * Sparse.eval nodeValue1433 x + ((1 : ℝ) * Sparse.eval nodeValue1436 x + ((1 : ℝ) * Sparse.eval nodeValue1437 x + ((1 : ℝ) * Sparse.eval nodeValue2769 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource380 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1656 x + ((1 : ℝ) * Sparse.eval nodeValue1657 x + ((1 : ℝ) * Sparse.eval nodeValue1661 x + ((1 : ℝ) * Sparse.eval nodeValue1745 x + ((2 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((1 : ℝ) * Sparse.eval nodeValue2290 x + ((2 : ℝ) * Sparse.eval nodeValue2584 x + ((1 : ℝ) * Sparse.eval nodeValue2603 x + ((2 : ℝ) * Sparse.eval nodeValue2717 x + ((2 : ℝ) * Sparse.eval nodeValue2735 x + ((2 : ℝ) * Sparse.eval nodeValue2738 x + ((1 : ℝ) * Sparse.eval nodeValue2761 x + ((2 : ℝ) * Sparse.eval nodeValue2762 x + ((2 : ℝ) * Sparse.eval nodeValue2763 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((1 : ℝ) * Sparse.eval nodeValue2784 x + ((2 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3118 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + 0))))))))))))))))))))

noncomputable def reducedSource381 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3098 x + ((2 : ℝ) * Sparse.eval nodeValue3572 x + ((2 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3623 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource382 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1404 x + ((1 : ℝ) * Sparse.eval nodeValue1408 x + ((1 : ℝ) * Sparse.eval nodeValue1418 x + ((1 : ℝ) * Sparse.eval nodeValue1440 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource383 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1404 x + ((1 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue2983 x + ((1 : ℝ) * Sparse.eval nodeValue3075 x + ((1 : ℝ) * Sparse.eval nodeValue3096 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

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

noncomputable def reducedSource384 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2090 x + ((1 : ℝ) * Sparse.eval nodeValue2962 x + ((1 : ℝ) * Sparse.eval nodeValue2983 x + ((1 : ℝ) * Sparse.eval nodeValue2995 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3572 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

noncomputable def reducedSource385 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1440 x + ((2 : ℝ) * Sparse.eval nodeValue2995 x + ((2 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3118 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource386 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2112 x + ((2 : ℝ) * Sparse.eval nodeValue2952 x + ((1 : ℝ) * Sparse.eval nodeValue2967 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

noncomputable def reducedSource387 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1418 x + ((2 : ℝ) * Sparse.eval nodeValue2962 x + ((2 : ℝ) * Sparse.eval nodeValue2967 x + ((1 : ℝ) * Sparse.eval nodeValue3098 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))

noncomputable def reducedSource388 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2516 x + ((1 : ℝ) * Sparse.eval nodeValue2520 x + ((1 : ℝ) * Sparse.eval nodeValue2521 x + ((2 : ℝ) * Sparse.eval nodeValue2719 x + ((1 : ℝ) * Sparse.eval nodeValue2737 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((1 : ℝ) * Sparse.eval nodeValue2789 x + ((2 : ℝ) * Sparse.eval nodeValue3035 x + ((1 : ℝ) * Sparse.eval nodeValue3049 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((2 : ℝ) * Sparse.eval nodeValue3063 x + ((2 : ℝ) * Sparse.eval nodeValue3072 x + ((2 : ℝ) * Sparse.eval nodeValue3075 x + ((2 : ℝ) * Sparse.eval nodeValue3086 x + ((2 : ℝ) * Sparse.eval nodeValue3098 x + ((1 : ℝ) * Sparse.eval nodeValue3101 x + ((1 : ℝ) * Sparse.eval nodeValue3121 x + ((2 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3161 x + ((1 : ℝ) * Sparse.eval nodeValue3225 x + 0))))))))))))))))))))

noncomputable def reducedSource389 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1292 x + ((2 : ℝ) * Sparse.eval nodeValue2588 x + ((1 : ℝ) * Sparse.eval nodeValue2740 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((1 : ℝ) * Sparse.eval nodeValue2783 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource390 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2132 x + ((1 : ℝ) * Sparse.eval nodeValue2134 x + ((1 : ℝ) * Sparse.eval nodeValue2138 x + ((1 : ℝ) * Sparse.eval nodeValue2278 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

noncomputable def reducedSource391 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1189 x + ((1 : ℝ) * Sparse.eval nodeValue1191 x + ((1 : ℝ) * Sparse.eval nodeValue1192 x + ((1 : ℝ) * Sparse.eval nodeValue1295 x + ((2 : ℝ) * Sparse.eval nodeValue2393 x + ((1 : ℝ) * Sparse.eval nodeValue2408 x + ((1 : ℝ) * Sparse.eval nodeValue2734 x + ((2 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((2 : ℝ) * Sparse.eval nodeValue2909 x + ((2 : ℝ) * Sparse.eval nodeValue2910 x + ((2 : ℝ) * Sparse.eval nodeValue2955 x + ((2 : ℝ) * Sparse.eval nodeValue3039 x + ((2 : ℝ) * Sparse.eval nodeValue3051 x + ((1 : ℝ) * Sparse.eval nodeValue3052 x + ((1 : ℝ) * Sparse.eval nodeValue3110 x + ((1 : ℝ) * Sparse.eval nodeValue3119 x + ((1 : ℝ) * Sparse.eval nodeValue3584 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

noncomputable def reducedSource392 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2405 x + ((1 : ℝ) * Sparse.eval nodeValue2408 x + ((1 : ℝ) * Sparse.eval nodeValue2409 x + ((1 : ℝ) * Sparse.eval nodeValue2744 x + ((2 : ℝ) * Sparse.eval nodeValue2841 x + ((1 : ℝ) * Sparse.eval nodeValue2842 x + ((1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3246 x + ((1 : ℝ) * Sparse.eval nodeValue3247 x + ((1 : ℝ) * Sparse.eval nodeValue3306 x + ((2 : ℝ) * Sparse.eval nodeValue3358 x + ((2 : ℝ) * Sparse.eval nodeValue3535 x + ((1 : ℝ) * Sparse.eval nodeValue3548 x + ((1 : ℝ) * Sparse.eval nodeValue3549 x + ((2 : ℝ) * Sparse.eval nodeValue3559 x + ((2 : ℝ) * Sparse.eval nodeValue3565 x + ((2 : ℝ) * Sparse.eval nodeValue3573 x + ((1 : ℝ) * Sparse.eval nodeValue3583 x + ((1 : ℝ) * Sparse.eval nodeValue3862 x + ((2 : ℝ) * Sparse.eval nodeValue3877 x + ((1 : ℝ) * Sparse.eval nodeValue3889 x + 0))))))))))))))))))))

noncomputable def reducedSource393 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2774 x + ((2 : ℝ) * Sparse.eval nodeValue3854 x + ((2 : ℝ) * Sparse.eval nodeValue3907 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))

noncomputable def reducedSource394 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1295 x + ((2 : ℝ) * Sparse.eval nodeValue2591 x + ((1 : ℝ) * Sparse.eval nodeValue2743 x + ((1 : ℝ) * Sparse.eval nodeValue2774 x + ((1 : ℝ) * Sparse.eval nodeValue2782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

noncomputable def reducedSource395 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1054 x + ((1 : ℝ) * Sparse.eval nodeValue1055 x + ((1 : ℝ) * Sparse.eval nodeValue1063 x + ((1 : ℝ) * Sparse.eval nodeValue1076 x + ((2 : ℝ) * Sparse.eval nodeValue2491 x + ((2 : ℝ) * Sparse.eval nodeValue2492 x + ((2 : ℝ) * Sparse.eval nodeValue2499 x + ((2 : ℝ) * Sparse.eval nodeValue2506 x + ((2 : ℝ) * Sparse.eval nodeValue2633 x + ((1 : ℝ) * Sparse.eval nodeValue2635 x + ((1 : ℝ) * Sparse.eval nodeValue2644 x + ((2 : ℝ) * Sparse.eval nodeValue2678 x + ((1 : ℝ) * Sparse.eval nodeValue2680 x + ((1 : ℝ) * Sparse.eval nodeValue2687 x + ((2 : ℝ) * Sparse.eval nodeValue2773 x + ((1 : ℝ) * Sparse.eval nodeValue2776 x + ((1 : ℝ) * Sparse.eval nodeValue2781 x + ((2 : ℝ) * Sparse.eval nodeValue3881 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3888 x + ((1 : ℝ) * Sparse.eval nodeValue4004 x + 0))))))))))))))))))))

noncomputable def reducedSource397 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue3055 x + ((2 : ℝ) * Sparse.eval nodeValue3884 x + ((1 : ℝ) * Sparse.eval nodeValue3886 x + ((1 : ℝ) * Sparse.eval nodeValue3913 x + ((1 : ℝ) * Sparse.eval nodeValue3963 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

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

noncomputable def reducedSource71 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2294 x + ((3 : ℝ) * Sparse.eval nodeValue3549 x + ((1 : ℝ) * Sparse.eval nodeValue3634 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))

end MUB6.Certificate.MixedSourceBridge

end OAI
end


