-- Prove2me | Definitions.Def_OAIQ106E187
-- name    : OAIQ106E187
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:32:20.338951+00:00
-- url     : https://prove2.me/theorems/ed4baa24-c6c1-42b7-81b1-0fc6d379c693
-- title:
--   Definitions bundle OAIQ106E187 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3455 declarations of OpenAI's Lean: 3455 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw20478Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20478step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20478step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20478step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20478step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20478step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20478step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20478step3`, `OAI.MUB6.Certificate.MixedSemantics.raw20478step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20479`, `OAI.MUB6.Certificate.MixedSemantics.raw20479Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step3`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step4`, `OAI.MUB6.Certificate.MixedSemantics.raw20479step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20480`, `OAI.MUB6.Certificate.MixedSemantics.raw20480Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step2`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step3`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step4`, `OAI.MUB6.Certificate.MixedSemantics.raw20480step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20481`, `OAI.MUB6.Certificate.MixedSemantics.raw20481Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20481step0`, `OAI.MUB6.Certificate.MixedSemantics.raw20481step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20481step1`, `OAI.MUB6.Certificate.MixedSemantics.raw20481step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw20481step2` and 3415 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical159`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical159.lean), [`MutuallyUnbiased_MixedSemantics_Canonical16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical16.lean), [`MutuallyUnbiased_MixedSemantics_Canonical160`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical160.lean), [`MutuallyUnbiased_MixedSemantics_Canonical161`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical161.lean), [`MutuallyUnbiased_MixedSemantics_Canonical162`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical162.lean), [`MutuallyUnbiased_MixedSemantics_Canonical163`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical163.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`.
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

def raw204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw204step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw205 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-2, 2, 0], ![0, 3, -3]]
def raw205Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw205step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw205step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw206 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw206step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw207 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw207Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw207step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw207step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20478step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw20479step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw20479step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2049step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2051Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw2051step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2051step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw2052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw2052step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw2052step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw2053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw2053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw2054Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2055 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2055step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2057Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw2057step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2057step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2058step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2060Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw2060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw2060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw2060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2061step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2061step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2063Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw2063step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2063step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2064step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2066Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2073step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2075 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2075Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2076step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2078Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw2078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2079step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2080 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2081Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2082step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2084Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw2084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2085step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2087 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2087Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2088step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2089 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2090Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2091step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2092 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw20480step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20480step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw20480step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20481step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20481step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20482step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20483step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20483step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20484step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20486step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20486step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20488step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20488step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20489step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20489step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20489step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20490step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20490step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20491step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20492step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20492step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20492step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20492step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20492step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20493step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20493step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20493step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20494step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20494step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20494step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20495step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20495step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20495step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20496step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw20496step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20496step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw20496step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20497step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20506step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20506step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20506step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20506step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20507step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20508step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20509step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw20509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20510step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20510step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20510step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20510step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20511step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20511step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20511step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20511step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20511step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20512step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20513step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20513step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20514step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20514step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20514step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20514step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20515step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20516step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20517step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20517step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20517step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20517step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20517step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20520step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20520step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20520step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw20520step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20520step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw20520step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20520step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw20520step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20521step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20521step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20522step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20522step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20523step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20523step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw20523step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20527step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw20527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw20530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw20533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20534step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20534step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20535step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20536step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20536step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20537step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20537step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20537step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20538step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20538step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20539step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20540step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20540step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20540step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20541step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20541step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20542step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20542step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw20543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20543step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw20543step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20543step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw20543step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20544step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20544step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20544step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20545step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20545step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20546step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20546step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 1, -2], ![4, -4, 0]]
def raw20547step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20547step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20547step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20547step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20547step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20548step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20548step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20548step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20548step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20548step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20549step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20549step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20549step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20549step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20549step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20550step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20550step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20550step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20550step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20554step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20557step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw20559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20560step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw20560step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20560step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw20560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20562step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20563step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20564step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 1, -2], ![4, -4, 0]]
def raw20564step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20564step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20565step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20566step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw20567step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20567step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20590 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20591 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20591step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20592 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20592step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20593 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![0, -3, 3]]
def raw20593step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20593step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw20593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20594 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, -2, 3]]
def raw20594step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20594step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw20594step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20597 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20598 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20598step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20599 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20599step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20600step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20601 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20602 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20603 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20603step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20604 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20604step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20605step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20606 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20607 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20607step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw20607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20608 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20608step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20609 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20609step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20609step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20610 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20610step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20610step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20610step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20610step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20611 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20611step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20611step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20612 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20612step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20613step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20614 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20614step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20615step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20615step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20616 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20616step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20617 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20617step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20618step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20618step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20619 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20619step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20619step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![1, -4, 3]]
def raw20619step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![3, 1, -4]]
def raw20619step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20620 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20620step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20620step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20620step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20621 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20621step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20622 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20622step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20623 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20623step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![0, -3, 3]]
def raw20623step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw20623step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20623step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw20623step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20624 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20624step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20624step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20624step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20625 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20627 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20627step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20628 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20628step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20628step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20628step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20628step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20629 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20630 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20630step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20631 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20631step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20631step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20631step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20631step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20631step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20632 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20632step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20632step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20634step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20635step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20636 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20636step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20636step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20636step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20637step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20637step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw20637step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20637step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw20637step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20638 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20638step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20639 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20639step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20639step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20639step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20639step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20640 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20640step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20640step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20641 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20641step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![1, -4, 3]]
def raw20641step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw20641step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20641step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw20641step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -3, 3]]
def raw20642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20644step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20648step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw20650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw20650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw20650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw20650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20651step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20652step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20655step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20656step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20660step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20661step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20662step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20662step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20663step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20664step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20665step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20667step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20674step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw20674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20675step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw20675step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20676step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20676step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw20676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw20681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw20686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20687step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20690step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20691step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw20691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20692step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw20696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20697step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20700step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw20700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20704step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw20704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw20704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20705step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20706step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw20706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20706step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20706step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20706step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20708step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw20709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw20711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw20714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw20716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20717step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw20717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20717step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20717step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20717step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw20718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw20719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20720step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20720step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20720step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20720step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw20721step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20721step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20721step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20722step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw20722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20722step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20722step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20722step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20722step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw20723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw20724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20725step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw20725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw20725step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20725step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw20725step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw20726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw20726step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20726step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw20726step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw20727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20727step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20727step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20727step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw20728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw20729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20730step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20730step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20731step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20731step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20738 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw20738Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20738step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw20738step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20738step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw20738step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20749step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20750step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20752step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20752step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20753step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20754step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20756step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20757step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20757step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20757step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20758step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20758step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20760step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20760step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20760step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20760step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20761step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20761step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20762step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw20764step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw20764step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw20765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw20765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20766step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw20768step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20768step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw20768step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20768step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw20768step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw20769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw20769step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20769step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20769step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20769step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20769step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20772step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20773step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20773step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20774step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20778step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20781step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20781step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20781step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20782step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw20785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20786step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw20786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20789step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw20789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw20789step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw20790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20790step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw20790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20790step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20795step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20798 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20798step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20803step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20803step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20817step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20821step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20827step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20827step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20827step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20830 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20830step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20830step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20830step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20842step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20843step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20844step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20845step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20846step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20849step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20850step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20853step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20853step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20854step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20855step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20857step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20857step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20858step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20859step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw20864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw20864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw20865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw20865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20865step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20866step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw20866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20870step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20874step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20874step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20875step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20876step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20878step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20878step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw20878step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20879step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20882step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20883step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20886step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20886step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw20886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw20887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20887step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20887step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20887step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20888step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20889step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw20889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20889step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20889step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20889step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20891step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20892step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20892step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20892step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20892step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw20893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20893step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20893step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20895step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20896step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20897step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20897step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20897step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20897step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20897step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20897step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20897step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20898step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20899step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20900step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20900step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20900step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20900step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20900step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20900step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20901step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20901step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw20901step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw20901step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20901step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw20901step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20902step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20903step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20903step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20904step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20904step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw20904step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20904step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw20904step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20905step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20905step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw20905step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw20905step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20905step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw20905step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20906step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20906step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20907step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20908Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20908step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20908step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20908step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20908step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20908step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw20909Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20909step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20909step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20909step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw20909step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20909step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw20909step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20916 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw20916Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw20916step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]
def raw20916step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw20916step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw20916step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw20916step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw20926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20926step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw20929step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw20929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end


