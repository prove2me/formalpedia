-- Prove2me | Definitions.Def_OAIQ106E192
-- name    : OAIQ106E192
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:34:12.055927+00:00
-- url     : https://prove2.me/theorems/bddc881f-d570-46cb-baf3-f371b83cdcca
-- title:
--   Definitions bundle OAIQ106E192 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2784 declarations of OpenAI's Lean: 2784 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw23608step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23608step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2360Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2360step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2360step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2360step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2360step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2360step2`, `OAI.MUB6.Certificate.MixedSemantics.raw2360step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23639`, `OAI.MUB6.Certificate.MixedSemantics.raw23639Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23639step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23639step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23639step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23639step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2364`, `OAI.MUB6.Certificate.MixedSemantics.raw23640`, `OAI.MUB6.Certificate.MixedSemantics.raw23640Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23640step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23640step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23640step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23640step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23641`, `OAI.MUB6.Certificate.MixedSemantics.raw23641Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23641step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23641step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23641step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23641step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23642`, `OAI.MUB6.Certificate.MixedSemantics.raw23642Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23642step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23642step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23642step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23642step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23642step2`, `OAI.MUB6.Certificate.MixedSemantics.raw23642step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23646`, `OAI.MUB6.Certificate.MixedSemantics.raw23646Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23646step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23646step0Labels` and 2744 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical18.lean), [`MutuallyUnbiased_MixedSemantics_Canonical184`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical184.lean), [`MutuallyUnbiased_MixedSemantics_Canonical185`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical185.lean), [`MutuallyUnbiased_MixedSemantics_Canonical186`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical186.lean), [`MutuallyUnbiased_MixedSemantics_Canonical187`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical187.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`.
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

def raw23Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw23step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw24 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]

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

def raw236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw237 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw237Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw237step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw238 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 3, -1]]
def raw238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw238step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw239 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 3, -1]]
def raw239Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw239step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw239step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw240 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2360Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw2360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2364 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2364step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2365 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2366 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2366Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2366step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2370 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2370step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2372 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2372Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2373 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2373step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2374 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2375 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2375Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw2375step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2375step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2376 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2376step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2377 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2378 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2378Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2378step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2378step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2378step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2379 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2379step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2380 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2381 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2381Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2381step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2382step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2383 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2384Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2384step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2385 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2385step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2386 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2387 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2387Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2387step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2387step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2387step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2388step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2389 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2390Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2390step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2390step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2390step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2391step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2393 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2393Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2393step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2393step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2393step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2394 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2394step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2395 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2396 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2396Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2397 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2397step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2398 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2399 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2399Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2399step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2400 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2400step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2401 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2402 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2402Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw2402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2403 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2403step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2404 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2405 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23646step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23646step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23646step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, 0, -2], ![2, -2, 0]]
def raw23662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23664step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw23665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![2, -1, -1], ![1, 0, -1]]
def raw23669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw23669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw23677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw23681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23683step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23694step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23694step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23694step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23694step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23695step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23695step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23695step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23696step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23696step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23696step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23696step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23697step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23697step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23698step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23698step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23698step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23698step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23703step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw23703step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23703step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw23703step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23703step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23715step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![3, -1, -2], ![1, 0, -1]]
def raw23718step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw23718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw23723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23724step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23724step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23724step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23724step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23726step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23727step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23728step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23729step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23729step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23729step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23729step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23729step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23731step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23731step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23732step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23732step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23732step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23732step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23733step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23733step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23733step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23733step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23740step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23741step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23744step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw23744step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23744step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23744step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23744step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23744step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23745step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23745step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23745step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23745step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23745step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw23746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23746step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23746step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw23747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![3, -1, -2], ![1, 0, -1]]
def raw23748step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw23748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw23748step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23748step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw23748step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23749step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw23749step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23749step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23749step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23749step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23750step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw23750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw23750step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23750step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw23750step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw23751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23751step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23751step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw23752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw23753step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw23753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw23753step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23753step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw23753step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23765step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23765step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23765step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23765step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23766 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23766step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23766step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23767step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23768step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23768step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23769step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23769step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23770step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23770step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23770step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23771step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23771step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23771step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23772step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23772step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23772step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23772step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23772step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23773step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23773step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23774 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23774step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23774step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23774step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23774step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23775step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23775step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23775step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23775step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23776step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23776step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23777step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw23777step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23778step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw23778step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23778step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23778step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23779step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw23779step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23779step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23779step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23780step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23780step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23780step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23780step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23780step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23781step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23781step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw23781step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23782step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23782step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23783step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw23783step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23783step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23783step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23784step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23784step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23784step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23784step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23785step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw23785step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23786step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23786step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23787step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23787step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![3, -3], ![2, -2]]
def raw23788step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23788step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]
def raw23788step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23789step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23789step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![3, -3], ![2, -2]]
def raw23789step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23789step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw23789step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23790step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![3, -3], ![2, -2]]
def raw23790step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23790step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw23790step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23791step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23791step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![3, -3], ![2, -2]]
def raw23791step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23791step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw23791step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![3, -3], ![1, -1]]
def raw23792step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23792step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw23792step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23793step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23794 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23795 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw23796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23797step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw23798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw23798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw23798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw23798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23799 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw23799Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23799step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw23799step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23799step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw23799step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23799step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23799step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw23802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw23802step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw23808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw23808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw23809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw23809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23810 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw23810Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23810step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw23810step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23810step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw23810step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23810step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23810step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw23816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw23816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw23816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23817 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw23817Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23817step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw23817step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23817step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw23817step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23817step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw23817step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23818 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23826 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw23826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw23827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw23827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23830 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw23836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23838 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]
def raw23838Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]
def raw23838step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw23838step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw23838step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23838step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23846 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23847 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23850 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23851 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw23851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw23851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23855 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw23857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw23857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw23865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23866 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw23866Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23866step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw23866step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23866step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw23866step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23866step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw23866step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23867 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23869 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw23882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23884 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23885 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23886 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23887 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw23888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23889 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw23889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw23895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw23898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw23903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw23904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw23910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23911 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw23911Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23911step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw23911step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23911step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw23911step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23911step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw23911step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23912 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23913 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23914 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw23914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23917 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23920 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw23932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw23932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw23936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw23936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23937 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23939 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23941step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23943step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23944 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw23945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw23946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw23947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw23948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw23948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23949 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23950 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw23950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23951 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23953 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw23954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw23954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw23961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw23963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw23964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw23964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw23965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw23965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw23965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23968 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-1, -1, 2]]
def raw23973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-1, -1, 2]]
def raw23973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw23973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw23973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23979 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw23981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw23981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23982 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23984 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw23990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw23990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw23991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw23991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw23991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23992 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![-2, 2], ![2, -2]]
def raw23992Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23992step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-2, 2], ![2, -2]]
def raw23992step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23992step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw23992step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw23996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw23996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw23997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw23997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw23998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw23999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw23999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw24001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24002 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw24002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw24004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw24005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw24005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw24006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw24006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw24009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24010 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24028 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw24028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24029 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw24029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24030 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw24030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24031 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw24032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw24035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24036 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24037 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24038 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24045 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw24045Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24045step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw24045step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24050 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw24050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24051 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw24051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24052 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


