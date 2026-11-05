-- Prove2me | Definitions.Def_OAIQ106E104
-- name    : OAIQ106E104
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:13:52.872577+00:00
-- url     : https://prove2.me/theorems/3bd5de3c-657f-44dc-be43-0c84da3b7f57
-- title:
--   Definitions bundle OAIQ106E104 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7492 declarations of OpenAI's Lean: 7492 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw29088step0`, `OAI.MUB6.Certificate.MixedSemantics.raw29088step1`, `OAI.MUB6.Certificate.MixedSemantics.raw29088step2`, `OAI.MUB6.Certificate.MixedSemantics.raw29088step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29088step3`, `OAI.MUB6.Certificate.MixedSemantics.raw29088step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29089`, `OAI.MUB6.Certificate.MixedSemantics.raw29089Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29089step0`, `OAI.MUB6.Certificate.MixedSemantics.raw29089step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29089step1`, `OAI.MUB6.Certificate.MixedSemantics.raw29089step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29089step2`, `OAI.MUB6.Certificate.MixedSemantics.raw29089step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29089step3`, `OAI.MUB6.Certificate.MixedSemantics.raw29089step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2908Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step2`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step3`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step4`, `OAI.MUB6.Certificate.MixedSemantics.raw2908step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2909`, `OAI.MUB6.Certificate.MixedSemantics.raw29090`, `OAI.MUB6.Certificate.MixedSemantics.raw29090Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29090step0`, `OAI.MUB6.Certificate.MixedSemantics.raw29090step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29090step1`, `OAI.MUB6.Certificate.MixedSemantics.raw29090step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29090step2`, `OAI.MUB6.Certificate.MixedSemantics.raw29090step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29091`, `OAI.MUB6.Certificate.MixedSemantics.raw29091Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29091step0`, `OAI.MUB6.Certificate.MixedSemantics.raw29091step0Labels` and 7452 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical22`, `MutuallyUnbiased_MixedSemantics_Canonical227`, `MutuallyUnbiased_MixedSemantics_Canonical228`, `MutuallyUnbiased_MixedSemantics_Canonical229`, `MutuallyUnbiased_MixedSemantics_Canonical23`, `MutuallyUnbiased_MixedSemantics_Canonical230`, `MutuallyUnbiased_MixedSemantics_Canonical231`, `MutuallyUnbiased_MixedSemantics_Canonical232`, `MutuallyUnbiased_MixedSemantics_Canonical233`, `MutuallyUnbiased_MixedSemantics_Canonical234`, `MutuallyUnbiased_MixedSemantics_Canonical235`, `MutuallyUnbiased_MixedSemantics_Canonical236`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35_e`.
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

def raw2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw2step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw29Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw29step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw30 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]

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

def raw292 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw292step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw293 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw293Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw293step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw293step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw293step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw294 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw295Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw295step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw295step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw297Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw297step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw298 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw299 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw299Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw299step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw299step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2]]
def raw2908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2]]
def raw2908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -3, 2]]
def raw2908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2908step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2908step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2908step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2909step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2909step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2909step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2909step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2909step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2909step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2909step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2910step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2910step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2910step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2910step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2910step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2910step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2910step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2911step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2911step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2911step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2911step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2911step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2911step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2911step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2912step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2912step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2912step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2912step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2912step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw2913step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw2913step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2914step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2914step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2914step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2914step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2915step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2915step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2915step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2915step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2915step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2916step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2916step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2916step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2916step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2916step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2917step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2917step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2917step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2917step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2917step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2918step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2918step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2918step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2919step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2919step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2919step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2920step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2920step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2920step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2921step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2921step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2921step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2921step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2921step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2921step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2922step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2922step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2922step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2922step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2922step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2923step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2923step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2923step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2924step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2924step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2924step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2925step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2925step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2925step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2925step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2926step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2926step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2926step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2927step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2927step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2927step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2927step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2927step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2927step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2928step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2928step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2928step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2928step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2929step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2930step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2930step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2931step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2931step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2931step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2932step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2932step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2932step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2933step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 3, 0], ![3, -3, 0]]
def raw2934step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw2934step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2935step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2935step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2935step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2935step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2935step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2935step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2935step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2936step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2936step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2936step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2936step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2936step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2936step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2937step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2937step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2937step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2937step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2937step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2937step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2937step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2938step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2938step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2938step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2938step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2938step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2939step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2939step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2939step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2940step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2940step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2940step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2941step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2941step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2941step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2941step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2942step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2942step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2942step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2942step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2943step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2943step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2943step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2943step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]

def raw29088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]

def raw29088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw29088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw29088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![4, -1, -3]]
def raw29092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw29092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-3, 1, 2]]
def raw29092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw29092step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29093step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29096step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw29096step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw29096step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29096step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29096step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29096step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29096step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29097step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29097step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29098step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29098step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw29098step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29098step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw29098step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29101step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw29101step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw29101step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29101step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw29101step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29102step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29102step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29102step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29105step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29106step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29106step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29107step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29108step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29109step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29109step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29111step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29111step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29111step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29111step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29113step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw29113step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw29113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29114step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29114step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw29114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29114step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw29114step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29115step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29116step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29117step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw29117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw29117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29118step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29118step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29118step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29118step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29118step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29119step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29121step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29121step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![4, -1, -3]]
def raw29122step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw29122step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw29122step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29122step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw29122step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29129 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw29129Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29129step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw29129step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29129step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29129step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29129step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw29129step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29148step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw29148step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29148step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29148step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29148step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29148step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29148step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29148step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29149step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29150step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw29152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29152step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29154step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29155step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29164step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29164step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29167step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29168step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29169step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29169step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29170step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29170step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw29171step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw29171step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29172step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29174step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29174step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29175step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29176 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29176step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29176step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29180 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29180step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -1, 1], ![0, -3, 3]]
def raw29182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-3, 3]]
def raw29182step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw29182step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw29182step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw29182step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw29182step4Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical228
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29184 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29184step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29184step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29186 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29186step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29186step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29190step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, -1, 1], ![0, -3, 3]]
def raw29208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw29208step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29208step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw29208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29209step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29209step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29209step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 0, 1], ![0, -3, 3]]
def raw29210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29210step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29210step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29210step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29210step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, -1, 1], ![-1, -2, 3]]
def raw29211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29211step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29211step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29211step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29211step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29212 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29212step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29212step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29212step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29212step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29213 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29213step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29214 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29214step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29214step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29215step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29216 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29216step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29216step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29216step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29216step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29217 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29217step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29218 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29218step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29219 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29219step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29219step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29219step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29219step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29220 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29220step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29220step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -3, 3]]
def raw29221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29221step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -2, 1], ![0, -3, 3]]
def raw29222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29222step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29223 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29223step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -2, 1], ![-1, -2, 3]]
def raw29224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw29224step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw29224step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, -1, 1], ![1, -4, 3]]
def raw29225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29225step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, -1, 1], ![1, -4, 3]]
def raw29226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29226step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29226step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29226step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29227 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29227step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw29228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw29228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 0, 1], ![1, -4, 3]]
def raw29228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29228step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29228step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29228step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw29229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29229step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw29230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw29231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![3, 0, -3]]
def raw29232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29232step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29232step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29232step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29233step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29233step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29233step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw29245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29248step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29248step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29250step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29251step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29251step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![3, 0, -3]]
def raw29251step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29251step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29251step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29251step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29252step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29252step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29252step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29253Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29253step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw29253step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29253step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29253step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29253step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29255Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29255step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29255step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29255step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29255step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29255step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29256step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw29256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29256step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29256step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29257step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw29257step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29257step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29257step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29257step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29259step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29259step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29259step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29259step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29260step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29260step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw29260step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw29260step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29261step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29261step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29262step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29263step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw29263step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29263step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29263step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29263step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29264step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29264step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw29264step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29264step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw29264step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29265Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29265step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29265step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29266step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29266step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw29267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw29272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw29273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29274step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29275step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29276step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29277step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29282step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29282step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw29287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw29287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29289step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29290step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29290step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29290step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw29291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw29291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw29294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29295step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29295step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29296step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw29296step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29296step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29296step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29297step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29297step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29298step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29298step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29299step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw29299step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29300step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]
def raw29300step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29300step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29300step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29300step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29300step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29301step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]
def raw29301step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29301step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29301step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29301step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29301step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29302step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29302step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![4, -4]]
def raw29302step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29302step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-2, 2], ![-3, 3]]
def raw29302step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29302step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw29302step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29303step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]
def raw29303step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29303step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29303step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29303step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29303step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29304step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]
def raw29304step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29304step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29304step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29304step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29304step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw29311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw29311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw29312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw29312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw29313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw29314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw29314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29315 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29319 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw29319Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29319step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![-2, 2], ![-2, 2]]
def raw29319step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29319step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw29319step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29319step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29319step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw29326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw29326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw29327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw29327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29328 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw29329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw29331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw29331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw29337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw29339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw29340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw29340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw29341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw29341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29342 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw29342Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29342step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw29342step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29342step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29342step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29342step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw29342step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw29349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw29350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29351 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw29351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw29351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw29352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw29352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29353 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw29353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw29354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw29354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw29355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw29355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw29356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw29356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw29358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw29358step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw29361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29365 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw29365Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29365step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw29365step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29365step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw29365step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw29366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, 0, -2], ![2, -1, -1]]
def raw29367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw29367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![3, -1, -2], ![2, -1, -1]]
def raw29370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw29370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw29370step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, 0, -2], ![3, -2, -1]]
def raw29371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-2, -1, 3], ![-3, 3, 0]]
def raw29371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw29371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29372 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw29372Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw29372step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![2, -2], ![1, -1]]
def raw29372step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw29372step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29372step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw29376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw29378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw29378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29379 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw29379Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29379step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29379step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29379step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29379step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw29383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw29383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw29384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29402 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29403 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29419 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29420 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw29420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29421 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw29421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29423 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw29423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 1, -3]]
def raw29435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0], ![2, 1, -3]]
def raw29435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw29435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29437 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw29437Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw29437step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]
def raw29437step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw29437step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29437step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29437step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -3, 1]]
def raw29438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -3, 1]]
def raw29439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2949step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2952step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2959step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2960step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2960step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2961step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2961step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2961step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2962step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2962step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0]]
def raw2963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2965step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2966step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2966step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2966step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2966step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2967step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2967step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw2968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2968step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2973step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2982step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2983step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2983step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2987step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2988step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2989step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0]]
def raw2993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2993step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2996step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw2998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2998step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw2999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3002step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3003step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3004step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3005step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3006step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3007step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3007step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3007step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3007step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3008step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3008step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3008step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3009step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3009step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3009step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3010step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3010step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3010step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3010step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3011step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3012step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3012step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3012step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3012step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3013step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3013step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3013step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3014step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3014step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3014step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3015step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3015step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3015step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3017step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3017step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3017step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3018step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3018step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3018step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3018step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3019step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3020step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3021step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3022step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw3023step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3023step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3024step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3024step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3025step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3026step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw29440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw29442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw29442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw29443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, -2, 1]]
def raw29443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29444 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2], ![-1, 1]]
def raw29444Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29444step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![-1, 1]]
def raw29444step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29444step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29444step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29444step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29444step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29445 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29447 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29448 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw29448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29449 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw29449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw29451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw29451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw29452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw29452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29453 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw29459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw29461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw29466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw29467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29468 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]
def raw29468Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29468step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw29468step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29468step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29468step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29468step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29468step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw29472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29474 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29475 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29476 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw29486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw29488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29491 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29493 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29494 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29495 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw29500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw29500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw29501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw29502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw29502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw29503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw29503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw29504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw29504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw29504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29505 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw29505Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29505step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29505step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw29511step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29511step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29511step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29511step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29512step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29512step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29512step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29512step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29513step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29513step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29513step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29514step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29514step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29514step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29514step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29518step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29522step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29524step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29524step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw29524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29524step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29525step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29526step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29527step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29527step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw29528step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29528step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0]]
def raw29531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29531step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29531step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29532step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29532step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29533step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29533step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29534step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29535step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29536step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29536step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29537step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29537step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29538step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29539step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29540step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29540step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29540step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29541step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29541step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29541step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29542step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -1, -2], ![1, -1, 0]]
def raw29544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29544step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw29545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0]]
def raw29548step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29557step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29558step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -1, -2], ![1, -1, 0]]
def raw29561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29562 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29562step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29563 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29563step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29564 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29564step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29565step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29565step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29566step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29567step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29567step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29568 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29568step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29569step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29570step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29570step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29571step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29571step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29572 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29572step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29573step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29574step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29575step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29576step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29577step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29578 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29578step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29579 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29579step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29580step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29581step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29582step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29582step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29583step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29583step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29584step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29584step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29584step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29585step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29586step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29586step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29587step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29588step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29588step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29589 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29589step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29589step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29590step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-3, 1, 2], ![1, -3, 2]]
def raw29591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw29591step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw29591step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29592 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29592step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29592step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29592step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29593 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29594 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29594step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29595 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29595step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29595step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29595step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29596step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29596step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29596step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29597 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29597step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29597step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw29597step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw29597step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29600step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw29600step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29600step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw29600step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29601 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29601step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29602 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29604 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29605step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29606 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29606step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29607step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29608 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29608step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29609 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29610 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29610step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29611 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29612step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw29612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw29612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29613 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29613step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29613step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29613step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29613step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29614 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29614step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29615step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29616step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29616step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29616step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29616step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29617 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29617step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw29617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw29617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29618 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29618step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29618step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw29618step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw29618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29619 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29619step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29620 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29621 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-3, 1, 2], ![1, -3, 2]]
def raw29621step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw29621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw29621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29632step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29632step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29632step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29632step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29633step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29633step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29633step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29634step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29634step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29635step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29639step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw29639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29639step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29649step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29650step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29651step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29652step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29653step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29654step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29655step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw29656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw29656step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw29656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29657step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29657step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29658step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29658step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29658step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -2, -1], ![1, 0, -1]]
def raw29659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw29663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw29663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw29670step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw29670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29671step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29672step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29672step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -2, -1], ![1, 0, -1]]
def raw29673step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29674 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29674step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29674step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29675 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29675step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29676 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29676step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29677step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29678step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29678step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29678step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29679 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29679step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29680 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29680step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29681step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29682step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29683step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29684step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29685step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29686step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29687step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29688step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29689step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw29690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29690step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw29691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29691step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29691step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29691step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29692 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29692step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29692step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29693 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29693step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw29694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw29694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw29694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29694step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29694step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29695step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29696 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29697 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29698step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw29704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw29704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw29704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw29709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw29709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw29710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw29710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29711 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3], ![0, 0]]
def raw29711Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]
def raw29711step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw29711step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29711step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw29711step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29712 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29735step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29736step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29736step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29737step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29738step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29738step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29739step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29740step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29741step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29742step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29743step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29744step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29745step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29745step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29746step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29747step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29748step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29748step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw29749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29753step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29754step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29754step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29755step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29755step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw29756step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29759step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw29759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw29759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw29760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29761step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw29765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29766step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw29770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29772step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29773step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw29780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw29781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw29785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw29786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29787step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29789step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw29790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29790step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw29791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw29791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw29791step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw29792step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29792step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw29793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw29794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw29794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw29794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw29795step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw29795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29795step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw29795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29796step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw29796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29796step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29796step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29796step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw29797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw29798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw29799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw29799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw29799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw29800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29800step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29800step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29800step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw29801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29801step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29801step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw29803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw29803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw29805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29805step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29805step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29805step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw29806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29806step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29806step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw29807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw29808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw29808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw29809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw29812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29825 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29825step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29829step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29860 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw29860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw29861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw29862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw29862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw29864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw29864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw29865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw29865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw29865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw29865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw29866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw29866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw29866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw29866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29867 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-2, 2], ![3, -3], ![1, -1]]
def raw29867Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29867step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![3, -3], ![1, -1]]
def raw29867step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29867step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29867step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29867step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29867step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw29898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw29899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw29899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29900 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]
def raw29900Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29900step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]
def raw29900step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29900step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw29900step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29900step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw29900step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw29905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw29906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29907 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw29907Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29907step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw29907step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29907step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw29907step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29907step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw29907step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw29911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, 2, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, 2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29913 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw29913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29914 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw29914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29918 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw29931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw29932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29933 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw29933Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29933step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw29933step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29933step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29933step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw29937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 1, -3], ![2, -2, 0]]
def raw29938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw29938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 1, -3], ![2, -2, 0]]
def raw29939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw29939step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw29942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw29942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, 0, -3], ![2, -2, 0]]
def raw29942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw29942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29942step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw29943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw29943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw29943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29944 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![3, -3], ![0, 0]]
def raw29944Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![3, -3]]
def raw29944step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]
def raw29944step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]
def raw29944step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29944step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29944step4Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw29979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29980step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29980step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29981step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29981step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29982step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw29983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29983step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29983step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29984step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29985step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29985step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29986step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29987step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29988step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29989step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29990step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29991step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29992step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29994step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw29996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw29996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![3, -1, -2], ![1, 0, -1]]
def raw29996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29996step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29997step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29997step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw29998step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw29998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29999step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29999step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29999step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29999step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30000step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30000step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30000step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30002step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30002step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30002step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30002step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30004step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw30005step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30005step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw30005step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30005step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw30005step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30005step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw30005step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw30007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30007step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30007step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30007step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw30009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw30011step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30011step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30011step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30012step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw30013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30013step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw30014step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw30014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw30014step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30014step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw30014step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, -1, -2], ![2, -1, -1]]
def raw30015step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30017step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30018step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![3, -1, -2], ![1, 0, -1]]
def raw30018step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30018step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw30018step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30018step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw30018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw30019step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30019step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30019step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30019step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30019step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30020step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw30020step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw30020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw30020step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30021Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30021step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30021step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30021step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30022step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30023step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw30024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, -1, -2], ![2, -1, -1]]
def raw30027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw30027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30032 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw30032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30032step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30032step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30037step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw30070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw30074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30075 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw30075Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30075step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw30075step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30075step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30075step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw30076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw30077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw30086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw30087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw30087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw30089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw30091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30091step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30092step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30092step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30092step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30093Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30093step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30094Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw30094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30095step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw30095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw30095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30096step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw30096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw30099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw30104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw30106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw30107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw30108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30110step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30113step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30114step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30115step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30115step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30116step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw30117step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30118step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30121step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30122step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30123step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw30125step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw30125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30126step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw30126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30126step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw30127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw30130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw30134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw30136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw30136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30139step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30140step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30142step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30145step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30146step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw30147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw30147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw30148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30148step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30149step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30150step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30150step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30150step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw30151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw30151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw30151step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30151step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30151step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30169 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30169step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30169step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30173 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30173step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30174 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30174step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30174step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw30199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical236
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1], ![-1, 0, 1]]
def raw30220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw30220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30224 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw30224Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30224step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw30224step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw30265step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30265step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30265step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30265step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw30266step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30266step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30266step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30267step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30267step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30267step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw30268step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw30268step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw30268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30269step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30269step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30269step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30269step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30270step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30270step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30270step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30272step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw30272step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30272step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30273step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30274step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30274step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30274step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30274step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30274step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30275Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30275step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30275step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30275step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30275step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30275step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30276Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30276step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30277step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw30277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30277step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30277step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30277step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30278step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30278step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30278step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30278step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30279step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw30279step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30279step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30279step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30279step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30280step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw30280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30280step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw30281step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30281step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30282step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw30282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30282step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30282step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30283step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30283step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30283step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30285step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw30287step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30288step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30288step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw30289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


