-- Prove2me | Definitions.Def_OAIQ106E194
-- name    : OAIQ106E194
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:35:22.903831+00:00
-- url     : https://prove2.me/theorems/ca4e2cac-66ff-4cd7-aac8-09736a869ef7
-- title:
--   Definitions bundle OAIQ106E194 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2739 declarations of OpenAI's Lean: 2739 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw24712step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24712step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24712step1`, `OAI.MUB6.Certificate.MixedSemantics.raw24712step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24712step2`, `OAI.MUB6.Certificate.MixedSemantics.raw24712step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24712step3`, `OAI.MUB6.Certificate.MixedSemantics.raw24712step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24713`, `OAI.MUB6.Certificate.MixedSemantics.raw24713Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step1`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step2`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step3`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step4`, `OAI.MUB6.Certificate.MixedSemantics.raw24713step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24714`, `OAI.MUB6.Certificate.MixedSemantics.raw24714Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24714step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24714step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24714step1`, `OAI.MUB6.Certificate.MixedSemantics.raw24714step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24714step2`, `OAI.MUB6.Certificate.MixedSemantics.raw24714step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24714step3`, `OAI.MUB6.Certificate.MixedSemantics.raw24714step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24715`, `OAI.MUB6.Certificate.MixedSemantics.raw24715Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24715step0`, `OAI.MUB6.Certificate.MixedSemantics.raw24715step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24715step1`, `OAI.MUB6.Certificate.MixedSemantics.raw24715step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24715step2`, `OAI.MUB6.Certificate.MixedSemantics.raw24715step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw24716`, `OAI.MUB6.Certificate.MixedSemantics.raw24716Labels` and 2699 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical19`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical19.lean), [`MutuallyUnbiased_MixedSemantics_Canonical193`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical193.lean), [`MutuallyUnbiased_MixedSemantics_Canonical194`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical194.lean), [`MutuallyUnbiased_MixedSemantics_Canonical195`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical195.lean), [`MutuallyUnbiased_MixedSemantics_Canonical196`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical196.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5416_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5417_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound89_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound90_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`.
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

def raw24Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]

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

def raw247Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw247step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw247step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw248 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw248step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw248step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw249 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw249Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw249step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw249step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

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

def raw2471Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2471step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2472 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2472step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2473 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2474Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw2474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2474step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2475step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2477Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2477step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2477step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2477step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2478step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2480 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2480Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2480step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2481 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2481step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2482 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2483 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2483Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2483step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2483step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2484step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2486Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2487 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2487step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2487step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2488 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2489 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2489Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw2489step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2489step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2490 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2490step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2491 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2492 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2492Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw2492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw2492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw2492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2493 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw2493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2493step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2494 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw2494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2495 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw2495Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2496 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2496step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2497 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2498 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2498Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2499 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2499step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2500 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2501 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2501Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2502 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2502step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2502step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2503 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2504 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2504Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2505 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2505step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2506 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2507 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2507Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2507step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2508 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2508step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2509 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2510 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2510Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2510step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2511 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2511step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2513Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2514 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2514step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2515 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2516Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2517 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2517step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2517step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2518 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical193
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24713step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24713step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24713step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24713step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw24715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24717step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24717step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24719step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24722step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24723step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24726step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw24727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw24727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24727step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw24727step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw24728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24728step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw24730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw24731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24731step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw24732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw24732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw24732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw24733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw24735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw24736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw24737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw24737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw24737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw24739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24739step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw24739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24739step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24739step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24739step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24739step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw24745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24746 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw24746Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24746step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw24746step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24746step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw24746step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw24751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw24755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24757step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24758step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24760step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24761step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24762step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24764step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24764step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24768step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24770step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24770step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24771step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24772step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24773step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24775step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw24780step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw24780step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw24781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw24781step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24794step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24794step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24805step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw24810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw24811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24815 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24815step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24818step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw24830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw24830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw24831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw24831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw24831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical194
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24832 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw24832Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24832step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw24832step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24832step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24832step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24832step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24832step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24839 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw24839Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24839step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw24839step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24839step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24839step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw24843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw24843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2]]
def raw24848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw24849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw24849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24850 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![0, 0], ![2, -2]]
def raw24850Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24850step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw24850step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24850step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw24850step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24857 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24857Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24857step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24857step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 0, 0], ![2, 1, -3]]
def raw24872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw24873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw24873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24874 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![3, -3]]
def raw24874Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw24874step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw24874step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw24874step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24874step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw24874step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24881 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw24881Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24881step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24881step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw24884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw24885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2]]
def raw24890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw24891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24892 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![0, 0], ![2, -2]]
def raw24892Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24892step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw24892step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24892step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24892step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24892step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24892step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24899 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24899Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 1, -3]]
def raw24913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw24914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24915 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]
def raw24915Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24915step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw24915step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24915step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24915step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24915step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24915step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24922 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]
def raw24922Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24922step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw24922step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24922step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24922step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw24926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw24926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw24931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw24931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw24932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw24932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24933 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1], ![-1, 1], ![1, -1]]
def raw24933Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24933step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![-1, 1], ![1, -1]]
def raw24933step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24933step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24933step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw24936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw24936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw24937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24944 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]
def raw24944Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24944step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw24944step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24944step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24944step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw24947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw24948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw24952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw24953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw24954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24955 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![0, 0], ![1, -1]]
def raw24955Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24955step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw24955step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24955step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24955step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical195
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24962 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]
def raw24962Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24962step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![0, 0], ![2, -2]]
def raw24962step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24962step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw24962step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24962step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw24962step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw24967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24969 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw24969Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24969step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw24969step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw24973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw24978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw24979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24980 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw24980Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24980step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw24980step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw24983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw24984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw24989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw24989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw24990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24991 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2], ![1, -1], ![-1, 1]]
def raw24991Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24991step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![-1, 1]]
def raw24991step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24991step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24991step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw24995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw24995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw25000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw25000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw25001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw25001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25002 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]
def raw25002Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25002step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![-1, 1], ![1, -1]]
def raw25002step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25002step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25002step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25025step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25025step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25025step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25025step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25025step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25026step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25026step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25026step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25027step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25027step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25028step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25028step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25029step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25029step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25030step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25030step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25030step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25031step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25031step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25032step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25033step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25033step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25034step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25034step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25035step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25036step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25037step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25037step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25038step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25038step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25039step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25039step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25039step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25040step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25040step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25040step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25041step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25041step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25041step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25042step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25042step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25043step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25043step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25043step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25043step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25044step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25044step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25044step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25046step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25046step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25046step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25046step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25047step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25047step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25048step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25049step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25049step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25049step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25050step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25061 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]
def raw25061Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25061step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw25061step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25061step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25061step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25067step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25068step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25069step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25069step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25069step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25070step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25071step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25072step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25073step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25074step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25075step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25076step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25087 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25087step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25089 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw25089step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25089step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25089step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25092 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25092step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25094 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25094step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25095step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25097step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25099 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25099step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25100step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25100step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25100step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25101step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25102step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25103step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25104 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25104step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25107 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25107step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25108 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25108step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25109 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25110 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25111 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25112 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25116 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25117 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25118 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25119 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25120 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25121 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25123step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25126 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25128 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25128step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25128step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25130step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25131 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25131Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25131step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25132 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25132step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25133step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25134 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25134step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw25164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25168step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25168step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw25168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25183step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


