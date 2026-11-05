-- Prove2me | Definitions.Def_OAIQ106E098
-- name    : OAIQ106E098
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:09:15.658005+00:00
-- url     : https://prove2.me/theorems/b8a014f1-f91b-4688-992c-b4ea9280444e
-- title:
--   Definitions bundle OAIQ106E098 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2742 declarations of OpenAI's Lean: 2742 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw22072Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22072step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22072step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22073`, `OAI.MUB6.Certificate.MixedSemantics.raw22073Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22073step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22073step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22073step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22073step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22076`, `OAI.MUB6.Certificate.MixedSemantics.raw22076Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22076step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22076step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22076step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22076step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22078`, `OAI.MUB6.Certificate.MixedSemantics.raw22078step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22078step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22078step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22078step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22079`, `OAI.MUB6.Certificate.MixedSemantics.raw22079Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22079step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22079step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2207Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2207step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2207step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2207step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2207step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2208`, `OAI.MUB6.Certificate.MixedSemantics.raw22080`, `OAI.MUB6.Certificate.MixedSemantics.raw22080Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22080step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22080step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22081`, `OAI.MUB6.Certificate.MixedSemantics.raw22081Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22081step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22081step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22081step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22081step1Labels` and 2702 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical17.lean), [`MutuallyUnbiased_MixedSemantics_Canonical172`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical172.lean), [`MutuallyUnbiased_MixedSemantics_Canonical173`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical173.lean), [`MutuallyUnbiased_MixedSemantics_Canonical174`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical174.lean), [`MutuallyUnbiased_MixedSemantics_Canonical175`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical175.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw221 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw221Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw221step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw222 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw223 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw223Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw223step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw223step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw224 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2207Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2207step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw2207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw2207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2208 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2208step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2209 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2210 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2210Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw2210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2210step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2211 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 3, -1]]
def raw2211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2211step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw2211step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw2211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2212 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 3, -1]]
def raw2212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2212step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw2212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2213 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 3, -1]]
def raw2213Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2213step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw2213step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw2213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2214 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2214step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2214step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2215 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2215step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2216 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2216Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2216step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw2216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw2216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw2216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2217 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2217step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2217step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2218 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2218step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2219 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2219Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2219step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2220 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2220step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2221 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2222 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2222Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw2222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2222step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2223 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2223step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2224 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2225 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2225Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw2225step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2225step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw2226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2226step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw2227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2228 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw2228Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2228step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2228step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2228step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2229 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2229step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2230 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2231 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2231Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2231step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2232 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2232step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2233 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2234 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2234Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw2234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw2234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw2234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2235 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw2235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2235step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2236 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw2236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2236step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw2236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2237 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw2237Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2237step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw2237step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw2237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw2237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22078 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]

def raw22078step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]
def raw22078step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22078step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22078step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw22083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22085 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw22085Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22085step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22085step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw22089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw22101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22103 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw22103Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22103step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]
def raw22103step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22103step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22103step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw22107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw22112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw22113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw22118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw22118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw22118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22120 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw22120Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22120step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![2, -2], ![1, -1]]
def raw22120step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22120step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw22120step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22120step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22120step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw22125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw22125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw22125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22131step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22131step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22131step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22131step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22132step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22132step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22132step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22132step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22133step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22133step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22133step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22134step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22134step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22134step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22135step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22135step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22135step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22140step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw22140step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22140step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw22160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22161step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22161step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22161step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22161step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22161step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22161step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22161step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22163step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22163step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22164step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22164step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22164step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22164step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22164step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22164step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22164step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22165step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22165step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22165step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22165step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22166step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22166step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22166step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22166step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22166step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22166step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22167step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22167step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22167step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22168step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22168step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22168step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw22168step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22169step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22169step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22169step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22169step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22169step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22169step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22170step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22170step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22170step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22171step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22171step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22171step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22171step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22175step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22177step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22179step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22181step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw22181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22181step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22181step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22181step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22182step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw22182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22182step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22182step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22182step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22182step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw22183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22183step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22183step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22183step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw22184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw22184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22185step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22185step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22185step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22185step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22185step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22186step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw22186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22186step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22186step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22186step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22187step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw22187step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw22187step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22187step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw22187step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw22188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw22189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw22189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw22190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw22190step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw22190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22190step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22190step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22190step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22190step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22197 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw22197Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22197step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![1, -1], ![2, -2]]
def raw22197step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22197step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22197step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw22205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw22205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw22206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw22206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22211 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22211step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22211step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22214step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22214step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22216step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22216step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22216step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22216step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22217step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22217step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22217step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22217step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22218 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22218step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22218step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22218step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw22221step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw22221step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22221step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw22221step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw22222step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22222step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22222step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw22223step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22223step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22223step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22223step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![3, 0, -3]]
def raw22224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw22224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22224step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw22224step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22224step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw22224step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22224step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw22224step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw22225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw22225step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22225step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22225step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22225step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw22228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![3, 0, -3]]
def raw22229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![3, 0, -3]]
def raw22229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22229step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw22229step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw22229step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw22229step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw22230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw22230step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22230step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22230step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22230step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22230step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw22235step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22235step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw22239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw22240step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22240step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22240step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22240step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw22249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw22249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw22250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw22250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![4, -1, -3]]
def raw22250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22250step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw22250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw22258step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22258step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22258step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22258step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22258step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw22259step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22259step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22259step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22259step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw22260step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22260step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22260step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22260step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw22261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22261step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw22261step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22261step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22261step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22261step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22261step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw22262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22262step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw22262step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22262step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22262step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22262step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22262step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22266step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22266step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22266step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22266step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22266step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22266step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw22267step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22267step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22267step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22267step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22271step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22271step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22271step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22271step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22271step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw22272step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22272step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22272step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22272step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22272step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22276step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22276step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22276step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22276step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22276step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw22277step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22277step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22277step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22277step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22277step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 0, -2], ![3, -1, -2]]
def raw22278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, 0, -2], ![2, 0, -2]]
def raw22282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22282step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw22282step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22282step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22283step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw22283step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -2, -2]]
def raw22287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -2, -2]]
def raw22287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 2, -2], ![4, -2, -2]]
def raw22287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw22287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22288step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22288step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22288step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22288step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22288step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22289 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22289step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22289step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22289step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22290step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22290step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22290step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22291step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22291step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22291step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22291step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22291step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22292 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22292step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22292step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22293 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22293step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22293step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -3, 1], ![-1, -2, 3]]
def raw22294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-2, -1, 3], ![-3, 2, 1]]
def raw22294step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22294step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw22294step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22294step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw22294step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw22295step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22295step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22295step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22295step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw22296step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22296step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22296step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22296step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22296step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw22297step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22297step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22297step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22297step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -2, 1], ![0, -3, 3]]
def raw22298step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-2, 1, 1], ![-3, 0, 3]]
def raw22298step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22298step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -1, -1], ![3, 0, -3]]
def raw22298step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22298step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -1, -1], ![3, 0, -3]]
def raw22298step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw22299step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22299step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22299step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22299step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw22300step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22300step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22300step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22300step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22301step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22301step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw22301step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22302step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw22302step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22302step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22302step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22303step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw22303step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22303step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22303step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22304step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw22304step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22305step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22305step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22306step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw22306step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22306step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22306step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22307step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22307step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw22307step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22308step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22308step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22308step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22309step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22309step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]
def raw22310step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22311step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22311step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw22311step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22312step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22312step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw22312step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22313step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22313step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw22313step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw22318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw22318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw22318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw22321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw22321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw22321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw22321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22323step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22329 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw22329Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw22329step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-2, 2], ![-2, 2]]
def raw22329step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw22329step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22329step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22338step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22341step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22361 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22362step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22363 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw22363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw22363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22364 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw22382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw22382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22384 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw22384Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22384step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw22384step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22384step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw22384step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22384step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw22384step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 1, -3]]
def raw22396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 1, -3]]
def raw22396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -3, 0], ![2, 1, -3]]
def raw22396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw22396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22398 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw22398Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw22398step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]
def raw22398step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw22398step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw22398step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw22398step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw22403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, 0, -2], ![1, -2, 1]]
def raw22404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22405 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![2, -2], ![-1, 1]]
def raw22405Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22405step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![-1, 1]]
def raw22405step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22405step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]
def raw22405step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22405step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw22405step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22406 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw22406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22407step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw22410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22410step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 0, 2], ![1, -3, 2]]
def raw22412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw22412step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw22412step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw22413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw22414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 1, 2], ![1, -3, 2]]
def raw22415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw22415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 0, 2], ![0, -2, 2]]
def raw22416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw22416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw22416step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw22417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22417step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw22418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22420 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw22428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw22428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw22431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw22431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22433 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw22434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw22444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw22444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw22449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw22449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22451 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def raw22455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw22458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw22461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw22461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw22462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw22462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22463 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw22463Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22463step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw22463step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22463step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw22463step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22470 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw22470Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22470step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22470step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22471step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22472step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22472step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22473step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22474step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


