-- Prove2me | Definitions.Def_OAIQ106E113
-- name    : OAIQ106E113
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:22:29.037908+00:00
-- url     : https://prove2.me/theorems/94502b5a-545d-42a2-bfbe-6f53964d2fb2
-- title:
--   Definitions bundle OAIQ106E113 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7402 declarations of OpenAI's Lean: 7402 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw41803Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41803step0`, `OAI.MUB6.Certificate.MixedSemantics.raw41803step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41803step1`, `OAI.MUB6.Certificate.MixedSemantics.raw41803step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41803step2`, `OAI.MUB6.Certificate.MixedSemantics.raw41803step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41804`, `OAI.MUB6.Certificate.MixedSemantics.raw41804Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41804step0`, `OAI.MUB6.Certificate.MixedSemantics.raw41804step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41804step1`, `OAI.MUB6.Certificate.MixedSemantics.raw41804step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41805`, `OAI.MUB6.Certificate.MixedSemantics.raw41805Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41805step0`, `OAI.MUB6.Certificate.MixedSemantics.raw41805step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41805step1`, `OAI.MUB6.Certificate.MixedSemantics.raw41805step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41805step2`, `OAI.MUB6.Certificate.MixedSemantics.raw41805step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41806`, `OAI.MUB6.Certificate.MixedSemantics.raw41806Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41806step0`, `OAI.MUB6.Certificate.MixedSemantics.raw41806step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41806step1`, `OAI.MUB6.Certificate.MixedSemantics.raw41806step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41806step2`, `OAI.MUB6.Certificate.MixedSemantics.raw41806step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41807`, `OAI.MUB6.Certificate.MixedSemantics.raw41807Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41807step0`, `OAI.MUB6.Certificate.MixedSemantics.raw41807step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41807step1`, `OAI.MUB6.Certificate.MixedSemantics.raw41807step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41807step2`, `OAI.MUB6.Certificate.MixedSemantics.raw41807step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41807step3`, `OAI.MUB6.Certificate.MixedSemantics.raw41807step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw41807step4` and 7362 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical3.lean), [`MutuallyUnbiased_MixedSemantics_Canonical32`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical32.lean), [`MutuallyUnbiased_MixedSemantics_Canonical326`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical326.lean), [`MutuallyUnbiased_MixedSemantics_Canonical327`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical327.lean), [`MutuallyUnbiased_MixedSemantics_Canonical328`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical328.lean), [`MutuallyUnbiased_MixedSemantics_Canonical329`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical329.lean), [`MutuallyUnbiased_MixedSemantics_Canonical33`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical33.lean), [`MutuallyUnbiased_MixedSemantics_Canonical330`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical330.lean), [`MutuallyUnbiased_MixedSemantics_Canonical331`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical331.lean), [`MutuallyUnbiased_MixedSemantics_Canonical332`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical332.lean), [`MutuallyUnbiased_MixedSemantics_Canonical333`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical333.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound70_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound71_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound72_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound75_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound76_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound77_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound78_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound80_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound81_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound82_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound83_e`.
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

def raw41Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw41step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw42 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]

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

def raw418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw418step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw419 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw419Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw419step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw420 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw420step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, 0, -2], ![3, -3, 0]]
def raw420step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, 0, -2], ![3, -3, 0]]
def raw420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw421 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw421Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw421step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw421step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw424 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw425 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw425Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw425step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw425step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw4180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4180step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw4184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw4186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4187step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw4189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw4191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4191step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4194step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw4194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4194step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4194step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw4195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw4195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4197step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw4201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw4203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw4204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4206 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw4206Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4206step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw4206step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw4207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw4212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw4213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw4214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw4215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical326
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41803Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw41803step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41803step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41804Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41805Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw41805step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41805step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41805step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41806Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw41806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw41806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41807Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41807step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw41807step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw41807step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41807step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41807step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41807step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41807step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41808Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw41808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw41808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41809Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41809step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw41809step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw41809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41810Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41810step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41811Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41811step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw41811step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41811step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41811step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41811step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41812Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41813Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41813step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41814Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41815Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41815step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41816Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw41816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw41816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41817Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41817step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41817step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41817step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41817step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41817step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41818Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41819Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41819step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw41819step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41819step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41819step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41819step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41820Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41821Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41821step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41821step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41821step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41821step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41822Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41823Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41824Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41825Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41825step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41825step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41825step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41826Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41827Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw41827step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41827step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41827step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41827step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41828Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41828step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41829Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41829step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41829step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41829step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41829step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41830Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41831Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41831step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41831step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41831step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41831step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41832Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41833Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41833step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41833step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41834Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41834step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![2, -3, 1]]
def raw41834step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw41834step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw41834step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41834step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw41834step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41835Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41835step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw41835step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41835step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![2, -3, 1]]
def raw41835step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41835step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw41835step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41836Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]
def raw41836step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw41836step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw41836step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41836step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw41836step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41837Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41837step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw41837step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41837step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]
def raw41837step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41837step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw41837step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41838Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw41838step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41838step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41838step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41838step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41839Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41839step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw41839step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw41839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41840Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41840step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw41840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41840step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41840step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41840step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41841Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41841step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41841step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41841step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41842Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw41842step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41842step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41842step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41842step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41843Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41843step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41843step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41844Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41844step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw41844step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41844step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41844step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41844step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41845Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41845step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41845step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw41845step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41845step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw41845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41846Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw41846step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41846step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41846step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41846step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41847Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41847step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw41847step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41848Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41848step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw41848step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41848step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw41848step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41849Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41849step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw41849step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41849step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41849step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41849step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41849step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41849step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41849step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41850Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41850step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41850step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41850step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41851Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41851step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41852Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw41852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41852step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41852step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41852step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41853Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41853step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41854Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41854step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41854step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41855Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41855step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical327
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41856Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw41856step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw41856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41857Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41857step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41857step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41857step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41857step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41857step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41858Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41858step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw41858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41858step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41858step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41858step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41859Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41859step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41860Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41861Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41861step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41862Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41862step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41863Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41864Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41864step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41865Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41865step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41865step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41866Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41867Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41867step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41867step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41867step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw41867step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41867step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw41867step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41867step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw41867step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41868Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41868step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41868step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41869Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41869step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41869step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw41869step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41869step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41869step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41869step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41869step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41870Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41870step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41871Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41871step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41871step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw41871step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41871step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41871step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41871step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41871step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41872Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41872step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41873Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41873step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw41873step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41873step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41873step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41873step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41874Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41874step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41875Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41875step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41875step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41875step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41875step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41876Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41876step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41877Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41877step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41877step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41877step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41878Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41878step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41879Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41879step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41879step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41879step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41880Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41880step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41881Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41881step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41881step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41881step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41881step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41881step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41882Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41882step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41883Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41883step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw41883step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41883step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41883step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41883step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41884Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41884step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41885Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41885step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41885step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41885step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41885step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41886Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41886step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41887Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41887step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41887step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41887step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41888Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41888step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41889Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41889step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41889step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41890Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41891Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41891step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41891step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41892Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41892step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41893Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41893step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41893step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw41893step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41893step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41893step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41893step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41893step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41894Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41895Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41895step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41895step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41895step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41895step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41895step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41895step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41895step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41896Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41896step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41897Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41897step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41897step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41897step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41898Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41899Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41899step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41899step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41899step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41899step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41899step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41900Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41900step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41900step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41901Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41901step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41901step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41901step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41901step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41902Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41903Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41903step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41903step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41903step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41904Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41905Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41905step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41905step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41905step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41905step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41906Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41907Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41907step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41907step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41908Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41909Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41909step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw41909step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41909step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41909step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41909step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41909step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41910Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41910step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41911Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41911step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41911step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41911step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41911step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41911step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41912Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41913Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw41913step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41913step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41913step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41914Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41914step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41915Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41915step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41915step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw41915step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41915step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41915step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41915step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41915step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41916Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41917Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41917step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41917step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw41917step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41917step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41917step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41917step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41917step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41918Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41918step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41919Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41919step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw41919step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41919step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41919step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41919step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41920Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41920step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41921Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41921step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41921step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41921step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41921step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41922Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41922step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41923Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41923step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw41923step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41923step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41923step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41923step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41924Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41924step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41924step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41925Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41925step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41925step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41925step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41925step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41925step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41926Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41926step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41927Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41927step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41927step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41927step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41927step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41928Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41928step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41928step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41928step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw41928step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41928step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw41928step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41929Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41929step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41929step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41929step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw41929step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41929step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw41929step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41930Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41930step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41930step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]
def raw41930step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -3, 4], ![-2, 1, 1]]
def raw41930step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw41930step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw41930step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41931Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41931step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41931step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41931step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]
def raw41931step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41931step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw41931step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41932Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41932step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw41932step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41932step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41932step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41933Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41933step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41933step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw41933step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41934Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw41934step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw41934step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw41934step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41935Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41935step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41935step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw41935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41936Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41936step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw41936step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw41936step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41937Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41937step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41937step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw41937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41938Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41938step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw41938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw41938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41939Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41939step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41939step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41939step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41939step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41939step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41939step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41940Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41941Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41941step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw41941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41942Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41942step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41943Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41943step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41943step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41943step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41943step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41943step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41944Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41945Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41945step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41945step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw41945step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41945step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41945step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41945step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41945step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41946Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41947Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41947step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41947step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41947step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41947step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41948Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41949Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41949step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41949step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41949step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41949step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41950Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41951Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41951step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41951step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41952Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41953Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41953step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41953step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41953step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41953step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41953step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41953step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41953step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41954Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41955Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41955step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41955step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41955step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41955step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41955step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41956Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41957Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41957step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41957step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41958Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41959Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41959step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41959step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41959step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41959step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41959step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41960Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41961Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw41961step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41961step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41962Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41963Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41963step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41963step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw41963step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41963step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41963step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41963step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41964Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41965Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41965step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41965step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41965step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41966Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41966step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41967Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41967step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41967step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41967step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41968Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41968step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41968step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw41968step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41968step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw41968step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41969Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41969step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41969step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41969step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw41969step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41969step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw41969step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41970Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41970step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41970step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41970step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41970step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41970step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41971Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41971step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41971step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw41971step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw41971step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41971step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw41971step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41972Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41972step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41972step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41973Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41973step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41973step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41973step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41973step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41973step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41973step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41974Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41974step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw41974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![3, -3, 0]]
def raw41974step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-3, 3, 0]]
def raw41974step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41974step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41974step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41975Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41975step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw41975step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41975step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![3, -3, 0]]
def raw41975step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41975step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41975step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41975step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41975step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41976Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41976step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw41976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw41976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41976step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41976step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41977Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41977step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw41977step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41977step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41977step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41977step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41977step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41978Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw41978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw41978step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41978step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41978step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41979Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41979step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw41979step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41979step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41979step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41979step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41979step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41980Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw41980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw41980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw41980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41981Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41981step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw41981step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw41981step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw41981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw41981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41982Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41982step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41982step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41982step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41983Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41983step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41983step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41983step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41983step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41983step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical328
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41984Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw41984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41985Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41985step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41985step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41985step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41985step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41986Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41987Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41987step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw41987step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41987step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41987step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41988Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41988step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41988step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41988step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41989Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41989step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw41989step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41989step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41989step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41990Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41990step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw41990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41991Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41991step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41991step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41991step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41991step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41992Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw41992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41993Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41993step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41993step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41993step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41994Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41994step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41994step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41995Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41995step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41995step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41995step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41996Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41996step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41997Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw41997step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41997step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41997step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41997step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41998Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41998step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41999Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41999step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41999step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42000Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42000step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42000step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42001Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42001step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42001step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42001step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42002Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42002step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42002step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42002step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42003Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42003step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42003step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw42003step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42003step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42003step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42003step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42004Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42004step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42004step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42005Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42005step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42005step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42005step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42005step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42005step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42005step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42005step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42005step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42006Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42006step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw42006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42006step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42006step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42007Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42007step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw42007step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42007step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42007step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42007step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42007step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42007step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42008Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42008step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42008step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42009Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42009step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42009step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42009step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42009step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42010Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42010step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42011Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42011step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42011step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42011step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42011step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42011step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42012Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42012step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42013Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42013step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42013step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42013step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42013step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42014Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42014step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42014step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42015Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42015step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42015step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42015step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42016Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42016step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42016step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42016step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42017Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42017step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42017step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw42017step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42018Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42018step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw42018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42018step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42018step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42019Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42019step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw42019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42020Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42020step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42020step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42020step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw42020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42020step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw42020step3Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42020step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw42020step4Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42020step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw42020step5Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42020step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw42020step6Labels : Fin 2 → Fin 1 := ![0, 0]

def raw42021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42021Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42021step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42021step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42021step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw42021step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42021step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw42021step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42021step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw42021step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42021step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw42021step5Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42021step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw42021step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw42022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42022Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42022step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42022step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42022step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42023Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42023step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42023step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw42023step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42023step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw42023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42024Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42024step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42024step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42024step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw42024step2Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42024step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw42024step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw42025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42025Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42025step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42025step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42025step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw42025step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42025step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw42025step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw42026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42026Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42026step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42026step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42026step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42026step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42027Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42027step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42027step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42027step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42027step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42028Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42028step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42028step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42029Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42029step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42029step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42029step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42029step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42030Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42030step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42030step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42030step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42030step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42031Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42031step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42031step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42032Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42032step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42032step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42033Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42033step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42033step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42033step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42034Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42034step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42035Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42035step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42035step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42036Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42036step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42036step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42037Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42037step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42037step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42038Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42038step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42039Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42039step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42039step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42040Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42040step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42041Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42041step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42041step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42041step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42041step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42042Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42042step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42042step1Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42042step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42042step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw42043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42043Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42043step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42043step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42043step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42043step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42043step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw42044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42044Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42044step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42045Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42045step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42046Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42046step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42047Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42047step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42047step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42048Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42048step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42049Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42049step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42050Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42051Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42051step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42051step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42051step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42052Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42052step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42052step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42053Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42053step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42053step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42053step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42053step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42053step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42053step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42054Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42055Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42055step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42055step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42056Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42056step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42057Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42057step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42057step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42057step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42057step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42058Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42058step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42059Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42059step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42059step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42059step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42060Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42061Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42061step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42061step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42061step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42062Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42062step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42063Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42063step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42064Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42064step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42064step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42065Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42065step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42066Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42067Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42067step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42068Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42068step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42069Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42069step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42069step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42070Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42071Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42071step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42072Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42072step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42073Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42073step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42073step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42074Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42075Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42075step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42076Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42076step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42076step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42077Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42077step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42077step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42077step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42077step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42077step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42078Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw42078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42078step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42078step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42078step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42078step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42079Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42079step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw42079step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42079step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42079step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42080Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42080step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42080step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42080step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42081Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42081step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42081step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42082Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42082step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42082step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42082step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42083Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42083step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42083step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42084Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42084step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42084step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42084step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42085Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42085step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42085step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42086Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42087Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42087step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42087step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42088Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42089Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42089step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42089step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42090Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42091Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42092Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42092step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42093Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42093step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42094Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42094step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42095Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42095step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42096Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42097Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42097step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42098Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42099Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42099step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw42099step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42099step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42099step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42100Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42100step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42100step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42101Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42101step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42101step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42101step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42101step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42101step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42102Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42102step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42102step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42103Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42103step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42103step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42103step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42103step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42103step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42104Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42104step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42104step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42105Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42105step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42105step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42105step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42106Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42106step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42107Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42107step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42107step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42108Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42109Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42109step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42109step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42109step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42110Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42111Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42111step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42111step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42111step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42111step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical329
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42112Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw42112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42112step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42112step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42112step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42113Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42113step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw42113step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42113step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42113step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42114Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42114step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42115Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42115step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42115step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42116Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42116step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42117Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42117step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42117step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42117step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42118Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42119Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42119step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42119step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42120Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42120step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42121Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42121step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42122Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42122step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42122step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42123Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42123step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42124Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42124step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42125Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42126Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw42126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42126step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42126step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42127Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42127step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42127step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw42127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42127step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42128Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42128step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42129Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42129step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42130Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42130step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]
def raw42130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -3, 0], ![-1, 2, -1], ![-2, 1, 1]]
def raw42130step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42130step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42130step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42131Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42131step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42131step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42131step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]
def raw42131step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42131step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw42131step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42131step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw42131step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42131step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw42131step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42132Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42132step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42133Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42133step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42133step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42133step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42134Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42134step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42135Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42135step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42135step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42135step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42135step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42135step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42135step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42135step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42136Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42137Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42137step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42137step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42137step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42137step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42137step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42137step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42138Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42138step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42138step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42138step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42138step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42138step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42138step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42139Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42139step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42139step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42139step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42139step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42140Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42140step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42141Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42141step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42141step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42141step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42141step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42141step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42142Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42142step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42142step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42142step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42143Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42143step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42143step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42144Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42144step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42144step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42145Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42145step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42145step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42145step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42145step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42145step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42146Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42146step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42146step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42146step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42146step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42146step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42147Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42147step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42147step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42147step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42147step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42147step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42148Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42148step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42148step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42149Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42149step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42149step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42150Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42150step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42150step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42151Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42151step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42151step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42151step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42151step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42152Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42152step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42153Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42153step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42153step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42154Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42154step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42154step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42155Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42155step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42155step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42155step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42156Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42157Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42157step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42157step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42158Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42158step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42159Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42159step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42160Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42161Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42161step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42162Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42162step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw42162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42162step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42162step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42163Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42163step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw42163step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42163step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42163step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42163step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42163step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42163step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42164Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42165Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42165step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42165step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42166Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42167Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42167step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42167step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42167step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42167step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42168Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42169Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42169step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42169step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42169step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42170Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42171Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42171step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42171step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42171step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42172Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42172step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42173Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42173step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42173step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42173step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42174Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42174step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42175Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42175step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42176Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42176step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42177Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42177step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42177step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42178Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42179Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42179step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42180Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42181Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42181step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42182Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42182step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42182step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42183Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42183step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42183step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42183step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42183step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42183step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42184Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42185Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42185step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42185step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42185step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42185step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42185step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42186Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42187Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42187step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42187step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42187step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42188Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42189Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42189step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42189step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42190Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42191Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42191step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42191step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42192Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42193Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42193step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42193step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42194Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42195Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42195step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42195step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42196Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42197Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42197step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42198Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42199Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42199step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42200Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42200step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw42200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw42200step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw42200step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42201Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42201step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw42201step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42201step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42201step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42202Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42202step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42203Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42203step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42203step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42203step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42204Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42205Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42205step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42205step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42205step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42206Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42206step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42207Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42207step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42207step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42207step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42208Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42209Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42209step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42209step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42209step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42210Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42210step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42210step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42211Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42211step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42212Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42213Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42213step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42213step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42213step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42214Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42215Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42216Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42216step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42217Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42218Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42219Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42219step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42220Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42220step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42221Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42222Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42222step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42223Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42223step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42223step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42223step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42223step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42224Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42224step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42224step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42224step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42224step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42224step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42225Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42225step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42225step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42225step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42225step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42226Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42227Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42227step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42228Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42229Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42229step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42229step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42229step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42230Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42231Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42231step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42231step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42231step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42232Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42232step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42233Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42233step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42234Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42235Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42235step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42235step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42235step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42236Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw42236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw42236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42237Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42237step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42237step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42238Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42239Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42239step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4229step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4230step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4234 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4235 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4235step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4235step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4236 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4236step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4236step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4236step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4236step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4236step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4244step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4244step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4244step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4248step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4248step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4248step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4252 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4253 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4254 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4254step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4254step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4254step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4254step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4254step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4262step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical330
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42240Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42240step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42240step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42240step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42241Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42241step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42242Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42242step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42242step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42243Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42243step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42243step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42243step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42244Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42244step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42245Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42245step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42246Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42247Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42247step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42248Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42248step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![2, -3, 1]]
def raw42248step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42248step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42249Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42249step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![2, -3, 1]]
def raw42249step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42249step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42249step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42249step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42249step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42250Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw42250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42250step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42250step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42251Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42251step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw42251step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42252Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42252step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42252step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42253Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42253step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42254Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42254step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42254step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42254step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42254step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42255Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42255step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42256Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42256step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42256step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42257Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42257step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42257step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42258Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42259Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42259step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42260Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42260step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42260step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42260step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42260step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42261Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42261step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42262Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42262step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42263Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42263step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42263step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42264Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42264step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42265Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42265step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42266Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42266step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42266step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42267Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42268Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42268step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42268step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42269Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42270Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42270step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42271Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42272Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42272step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42272step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42272step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42273Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42274Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42275Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42276Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42276step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42276step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42276step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42277Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42277step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42277step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42277step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42277step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42278Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42278step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42278step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42278step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42278step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42279Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42279step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42280Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42280step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42280step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42281Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42281step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42282Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42282step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42283Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42283step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42284Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42285Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42286Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42287Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42288Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42289Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42289step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42289step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42289step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42289step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42290Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42291Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42291step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42292Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42293Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42293step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42293step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42293step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42294Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42294step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42294step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42295Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42295step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42295step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42296Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42297Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw42297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42298Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw42298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42298step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42298step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42298step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42299Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42299step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw42299step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42299step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42300Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw42300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42300step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42300step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42300step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42301Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42301step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw42301step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42301step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42302Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42302step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42303Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42303step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42303step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42303step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42304Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42304step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42304step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42304step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42305Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42305step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42306Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42306step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42306step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42306step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42307Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42307step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42308Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42309Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42309step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42310Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42310step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42310step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42311Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42312Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42312step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42313Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42313step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw42313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw42313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42314Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42314step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42315Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw42315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42316Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42317Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42318Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42318step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42318step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42318step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42319Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42319step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42319step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42320Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42321Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw42321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42322Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw42322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw42322step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42322step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42322step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42323Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42323step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw42323step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42323step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42323step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42323step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42324Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42325Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42325step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw42325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42326Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42326step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42327Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42327step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42327step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42328Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw42328step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-3, 3, 0]]
def raw42328step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw42328step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw42328step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42329Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42329step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42329step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42329step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw42329step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42329step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw42329step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42329step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw42329step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42330Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw42330step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42330step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42330step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42331Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42331step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42331step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw42331step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42331step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42331step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42331step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42331step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42332Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42332step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42332step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42332step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42333Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42333step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42333step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42333step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42333step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42333step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42333step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42334Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42334step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42334step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42334step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42334step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42335Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42335step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42335step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42335step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42335step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42335step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42335step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42335step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42336Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42336step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw42336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42336step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw42336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42337Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42337step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42337step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw42337step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42337step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw42337step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42338Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42338step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42338step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42338step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42338step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42339Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42339step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42339step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42339step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42339step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42339step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42340Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42340step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42340step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42340step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42340step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42341Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42341step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42341step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42341step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42341step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42341step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42342Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42342step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42342step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42342step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42342step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42342step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42343Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42343step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42343step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42343step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42343step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42343step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42344Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42344step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42344step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42344step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42344step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42344step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42345Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42345step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42345step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42345step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42345step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42345step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42346Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42346step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw42346step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw42346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42347Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42347step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw42347step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw42347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42348Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42348step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42348step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42348step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42348step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42348step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42349Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42349step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42349step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42349step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42349step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42350Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42350step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42350step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42350step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42350step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42351Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42351step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42351step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42351step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42351step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42351step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42352Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42352step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42353Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42353step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42353step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42354Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42355Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42355step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42355step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42355step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42356Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42356step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42356step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42357Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42357step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42357step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42358Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42359Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42359step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42359step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42360Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw42360step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42360step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw42360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42361Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42361step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42361step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42361step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42361step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42361step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42361step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42361step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42362Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42363Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42363step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42363step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42364Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42365Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42365step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42365step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42365step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42365step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42366Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42366step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42367Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42367step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical331
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42368Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42368step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42368step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42369Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42369step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42369step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42369step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42370Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42371Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42371step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42371step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42371step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42372Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42373Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42373step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42373step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42374Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42374step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42375Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42375step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42376Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42376step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42377Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42378Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42378step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42379Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42379step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42380Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42380step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42381Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42381step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42382Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42383Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42384Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42384step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42384step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42384step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42384step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42385Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42385step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42385step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42385step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42385step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42385step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42386Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42386step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42386step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw42386step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42386step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw42386step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42387Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42387step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42387step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42387step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42387step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42388Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42388step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42389Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42389step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42389step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42390Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42390step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw42390step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42390step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42391Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42391step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42391step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42392Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw42392step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42392step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42392step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42392step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42393Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42393step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw42393step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw42393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42394Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42394step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42394step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42395Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42395step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42395step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42396Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42397Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42397step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42397step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42397step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42397step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42397step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42398Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw42398step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42398step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42398step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42399Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42400Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42400step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42401Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42401step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42401step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42401step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42402Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42403Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42403step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42403step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42404Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42404step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42405Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw42405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42406Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42406step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw42406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42406step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42406step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42407Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42407step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw42407step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42407step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42407step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42407step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42407step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42407step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42407step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42408Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42409Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42409step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42409step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42410Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42411Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42411step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42411step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42411step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42411step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42411step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42412Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42413Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42413step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42414Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42415Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42415step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42415step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42415step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42416Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42416step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42417Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42417step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42418Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42418step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42419Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42419step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42419step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42419step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42419step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42420Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42420step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42420step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42420step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42421Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42422Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42422step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42423Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42424Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42425Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42425step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42426Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42426step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42426step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42427Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42428Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42429Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42430Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42430step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42430step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42431Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42431step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42431step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42431step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42431step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42432Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42432step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42433Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42433step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42434Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42435Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42435step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42435step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42435step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42436Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42437Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42438Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42438step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42439Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42439step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42440Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42440step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42441Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42441step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42441step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42441step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42442Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42443Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42443step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42443step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42444Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42444step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42445Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42445step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42445step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42446Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42446step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42446step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42447Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42448Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42449Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42449step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42449step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42450Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42450step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42451Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42451step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42452Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42453Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42453step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42453step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42453step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42454Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42454step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42454step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42455Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42455step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42455step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw42455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42456Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42456step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42456step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42457Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42457step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42458Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42458step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42458step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42458step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42458step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42459Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42459step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42460Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42460step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42461Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42461step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42462Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42462step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42463Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42463step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw42463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42464Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42464step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42464step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42464step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42464step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42465Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42465step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42466Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42466step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42467Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42467step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42467step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42467step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42468Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42468step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42469Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42469step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42470Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42470step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42470step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42471Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42472Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42472step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42472step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42472step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42473Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42474Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42475Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42475step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42475step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42475step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42476Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42476step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42476step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42476step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42477Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42478Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42479Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw42479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42480Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw42480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw42480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw42480step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw42480step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw42480step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42481Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw42481step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw42481step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw42481step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42481step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw42481step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42481step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw42481step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42482Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw42482step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw42482step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw42482step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42482step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw42482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42483Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw42483step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42484Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw42484step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42484step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42484step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42484step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42484step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42485Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw42485step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42485step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42485step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42485step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42485step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42486Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw42486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42486step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42486step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42487Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw42487step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42487step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42488Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw42488step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw42488step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42488step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42488step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42488step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42489Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw42489step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42490Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42491Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42492Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42492step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42493Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42494Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42494step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42494step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42495Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical332
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42496Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42496step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42497Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42498Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw42498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42499Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42499step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42500Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42500step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42501Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42501step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42502Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42502step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42503Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42504Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw42504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw42504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw42504step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42504step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw42504step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42505Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw42505step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42505step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42505step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42505step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42506Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw42506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw42506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42507Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42507step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42508Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42509Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42509step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42510Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42511Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42512Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42513Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42513step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42513step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42514Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw42514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw42514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw42514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42515Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw42515step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw42515step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw42515step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42516Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw42516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw42516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw42516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42517Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw42517step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42517step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42517step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42518Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42519Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42520Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw42520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw42520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42520step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw42520step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42521Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw42521step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw42521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42522Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw42522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42523Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42523step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42524Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42525Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42525step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42526Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42526step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42527Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42528Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42529Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42529step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42529step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42530Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw42530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw42530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42531Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw42531step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw42531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42532Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw42532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw42532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42533Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42533step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42534Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw42534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw42534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw42534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42535Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw42535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42536Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw42536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw42536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw42536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42537Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw42537step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42538Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42538step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42539Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42540Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42540step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42541Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42542Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42542step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42543Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42544Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw42544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw42544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42545Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42546Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42546step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42547Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42548Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42549Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42549step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw42550Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw42550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 3, -4], ![2, -3, 1]]
def raw42550step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw42550step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw42550step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw42550step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw42551Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw42551step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 3, -4], ![2, -3, 1]]
def raw42551step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw42552Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw42552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -3, 2], ![2, 3, -5]]
def raw42552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw42552step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42552step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42552step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw42553Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw42553step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -3, 2], ![2, 3, -5]]
def raw42553step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42554Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42554step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42554step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42554step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42554step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42555Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42555step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42556Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42556step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42556step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42557Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42557step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42558Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42558step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42558step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42558step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42559Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42559step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw42560Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw42560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42560step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42560step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42560step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw42561Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw42561step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw42562Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw42562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw42562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw42562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw42563Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw42563step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42564Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42564step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42565Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42566Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42566step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42567Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42568Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42568step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42569Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42570Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42570step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42571Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42572Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42572step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42572step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42573Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42574Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42574step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42574step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42575Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42576Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw42576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw42576step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42576step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42576step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42576step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42577Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw42577step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42578Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw42578step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42578step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42578step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42578step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42579Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw42579step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42580Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw42580step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42580step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42580step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42580step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42581Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw42581step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42582Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42582step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42582step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42582step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42583Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42584Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42584step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42584step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42584step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42585Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42586Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42586step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42586step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42586step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42587Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42588Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42588step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42589Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw42589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42589step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42589step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42589step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42590Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42590step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42591Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw42591step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42591step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42591step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42592Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42593Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw42593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42593step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42593step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42594Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42594step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42595Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42595step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42596Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw42596step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw42596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw42596step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42596step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw42596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42597Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw42597step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw42597step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw42597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42598Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw42598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42598step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42599Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw42599step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw42599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42600Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42600step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42601Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42602Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42603Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42604Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42604step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42605Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw42605step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42606Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw42606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw42606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw42606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42607Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw42607step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw42607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42608Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw42608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42608step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42608step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42608step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42609Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42609step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42610Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw42610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42610step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42610step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42610step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42611Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw42611step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42612Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42613Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42614Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42615Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42616Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42617Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42618Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42619Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw42619step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42619step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42620Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw42620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw42620step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42620step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42620step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42621Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42621step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw42621step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42622Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw42622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42622step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42622step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42623Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42623step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw42623step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical333
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42624Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42624step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42624step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42624step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42625Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42625step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42626Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42627Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42627step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42628Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42628step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42628step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42628step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42629Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42629step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42630Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42630step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42630step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42631Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42631step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42632Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42632step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42633Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42634Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42635Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42636Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42636step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42636step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42636step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42636step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42637Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42637step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42638Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42638step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42638step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42639Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42640Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42641Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw42641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42642Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42642step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw42642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw42642step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw42642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42643Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42643step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw42643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw42643step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42644Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42645Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw42645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw42645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42646Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw42646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw42646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42647Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw42647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw42647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42648Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42648step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42648step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42648step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42648step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42649Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42649step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42650Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42650step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42650step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42651Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw42651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw42651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42652Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42653Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw42653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42654Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42654step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw42654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42654step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42654step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42654step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42655Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42655step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw42655step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42656Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42656step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42656step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42656step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42656step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42656step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42657Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42657step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42658Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42658step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42658step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42658step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42659Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42659step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42660Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42660step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw42660step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42660step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42660step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42661Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42661step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42661step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw42661step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42661step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42661step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42661step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42662Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42662step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42662step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw42662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42662step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42662step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42663Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42663step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42663step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw42663step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42663step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42663step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42663step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42664Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42664step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -2, 3], ![-2, 1, 1]]
def raw42664step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw42664step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw42664step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42665Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42665step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42665step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw42665step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42665step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42665step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42665step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42666Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42666step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42666step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42666step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42667Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42667step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw42667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42667step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42668Labels : Fin 3 → Fin 2 := ![1, 1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


