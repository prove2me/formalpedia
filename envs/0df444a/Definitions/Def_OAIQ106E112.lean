-- Prove2me | Definitions.Def_OAIQ106E112
-- name    : OAIQ106E112
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:21:09.226261+00:00
-- url     : https://prove2.me/theorems/be4adbc5-4a3d-4211-a4f5-00ee1778f4e3
-- title:
--   Definitions bundle OAIQ106E112 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7460 declarations of OpenAI's Lean: 7460 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw40793step1`, `OAI.MUB6.Certificate.MixedSemantics.raw40794`, `OAI.MUB6.Certificate.MixedSemantics.raw40794Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40794step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40794step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40794step1`, `OAI.MUB6.Certificate.MixedSemantics.raw40794step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40795`, `OAI.MUB6.Certificate.MixedSemantics.raw40795Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40795step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40795step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40796`, `OAI.MUB6.Certificate.MixedSemantics.raw40796Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40796step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40796step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40797`, `OAI.MUB6.Certificate.MixedSemantics.raw40797Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40797step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40797step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40797step1`, `OAI.MUB6.Certificate.MixedSemantics.raw40797step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40797step2`, `OAI.MUB6.Certificate.MixedSemantics.raw40797step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40797step3`, `OAI.MUB6.Certificate.MixedSemantics.raw40797step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40798`, `OAI.MUB6.Certificate.MixedSemantics.raw40798Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40798step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40798step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40798step1`, `OAI.MUB6.Certificate.MixedSemantics.raw40798step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40798step2`, `OAI.MUB6.Certificate.MixedSemantics.raw40798step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40799`, `OAI.MUB6.Certificate.MixedSemantics.raw40799Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40799step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40799step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40799step1`, `OAI.MUB6.Certificate.MixedSemantics.raw40799step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40799step2` and 7420 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical3`, `MutuallyUnbiased_MixedSemantics_Canonical31`, `MutuallyUnbiased_MixedSemantics_Canonical318`, `MutuallyUnbiased_MixedSemantics_Canonical319`, `MutuallyUnbiased_MixedSemantics_Canonical32`, `MutuallyUnbiased_MixedSemantics_Canonical320`, `MutuallyUnbiased_MixedSemantics_Canonical321`, `MutuallyUnbiased_MixedSemantics_Canonical322`, `MutuallyUnbiased_MixedSemantics_Canonical323`, `MutuallyUnbiased_MixedSemantics_Canonical324`, `MutuallyUnbiased_MixedSemantics_Canonical325`, `MutuallyUnbiased_MixedSemantics_Canonical326`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound42_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound44_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound45_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound47_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound48_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound50_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound51_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound52_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound54_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound57_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound58_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound59_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound60_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound61_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound64_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound65_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound66_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound67_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound68_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound70_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`.
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

def raw40Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw40step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw40step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw40step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw40step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]

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

def raw407Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw407step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw407step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw408 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw409 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw409Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw409step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw411 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw411Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw411step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw412 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw413 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw413Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw413step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw414 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw415 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw415Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw415step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw416 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw416step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw417 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw417Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw417step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw418 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw4079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4079step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4084step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4086 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4086step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4087 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4088 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4089 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4090 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]
def raw4091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw4091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw4091step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw4092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4093 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw4093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4094 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw4094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4094step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical318
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]

def raw40794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40794step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40797step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40810step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40811step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40811step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw40811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw40820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw40821step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw40821step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40821step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw40822step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![3, -1, -2]]
def raw40823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40825step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40826step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw40827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical319
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40840step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw40843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw40850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw40850step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40850step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw40850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40850step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw40850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![3, -2, -1]]
def raw40851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![3, -1, -2]]
def raw40852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw40853step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw40854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw40855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw40860step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw40866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw40867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw40872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw40874step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw40875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -3, 2], ![2, 3, -5]]
def raw40880step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![3, -2, -1]]
def raw40887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![3, -2, -1]]
def raw40887step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![3, -1, -2]]
def raw40888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw40889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw40890step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40891Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw40891step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40892Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw40894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]
def raw40894step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw40894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw40894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw40895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw40895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw40895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw40899step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw40900step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw40905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw40905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw40906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw40907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw40908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw40913step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40914step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw40914step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw40917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![3, -1, -2]]
def raw40917step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw40918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw40919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw40920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![3, -1, -2]]
def raw40920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw40920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40921step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw40923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40923step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw40924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw40926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw40926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40927step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw40928step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40928step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw40929step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 3, -4], ![2, -1, -1]]
def raw40931step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40931step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw40932step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![2, -3, 1]]
def raw40933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40933step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]
def raw40933step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40933step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw40933step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![2, -2, 0]]
def raw40934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![2, -1, -1]]
def raw40935step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![2, 0, -2]]
def raw40936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw40936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40937step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40939step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40940step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40941step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40942step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![2, -3, 1]]
def raw40947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw40947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw40947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw40948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40956step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -3, 3], ![2, 1, -3]]
def raw40958step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw40958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40958step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw40958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40959step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40959step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40959step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw4096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4097step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4097step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw4097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw4100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4100step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -2, 0], ![2, 1, -3]]
def raw4100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4104 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4105 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4106 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4108 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4109 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw4170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw4170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4173step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw4174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw4175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw4175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4175step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw4175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw4179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4179step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical320
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw40964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw40967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw40967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw40968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw40968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw40972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -3, 3], ![2, 2, -4]]
def raw40976step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw40976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 2, -3], ![1, -3, 2]]
def raw40977step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw40983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw40986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw40986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw40986step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40986step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 3, -5]]
def raw40986step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40986step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw40986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw40987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw40987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw40987step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw40988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw40988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw40988step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw40989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw40989step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw40989step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw40990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw40990step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw40990step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw40990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw40991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw40991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw40991step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw40991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40991step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw40991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw40995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw40995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw40997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![3, -2, -1]]
def raw40998step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40998step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![3, -2, -1]]
def raw40998step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40998step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -2, 3], ![-2, 3, -1]]
def raw40998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40998step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw40998step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![3, -1, -2]]
def raw40999step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-2, 3, -1], ![-2, -1, 3]]
def raw40999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw40999step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41000step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41000step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-2, 2, 0], ![-2, -1, 3]]
def raw41000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41000step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw41000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw41001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw41002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41003step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41003step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw41004step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41005step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41006step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41011step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41011step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw41011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41013Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41013step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41014Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41014step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw41014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41015Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41015step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41016Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw41016step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw41016step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw41016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![3, -1, -2]]
def raw41017step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41018Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41018step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41019step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw41019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41020step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41020step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41022step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41025step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw41025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41025step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41026step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41027step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw41028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw41028step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw41028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41029step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41030step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41031step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -2, -1]]
def raw41032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![3, -2, -1]]
def raw41032step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![3, -1, -2]]
def raw41033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]
def raw41038step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 3, -1]]
def raw41038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw41038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw41039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw41042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw41042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, -1, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 3, -1]]
def raw41048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1]]
def raw41048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw41052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41056step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw41057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw41057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw41059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![3, -1, -2]]
def raw41059step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41059step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw41064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw41066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw41068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw41068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 3, -4], ![2, -1, -1]]
def raw41068step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![2, -2, 0]]
def raw41070step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41070step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]
def raw41070step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41070step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41070step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![2, -1, -1]]
def raw41071step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![2, 0, -2]]
def raw41072step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41073step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41074step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41075step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw41079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw41079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw41079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw41079step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw41080step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41080step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41081step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]
def raw41087step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41087step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw41087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical321
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41088Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41088step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41088step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw41088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw41088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41089Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41089step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41090Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41090step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41091Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41091step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41092Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41093Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41094Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw41094step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41096step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![2, 2, -4]]
def raw41096step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41097step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 2, -3], ![1, -2, 1]]
def raw41097step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41098step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw41100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41102step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41102step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 3, -5]]
def raw41102step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41102step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw41102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw41103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw41103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw41103step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41103step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 3, -4], ![1, -2, 1]]
def raw41103step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41103step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw41103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41105step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw41106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw41106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw41106step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41107step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![3, -1, -2]]
def raw41110step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41110step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![3, -1, -2]]
def raw41110step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41110step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-2, 3, -1], ![-2, -1, 3]]
def raw41110step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41110step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw41110step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41111step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw41111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41111step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![3, -1, -2]]
def raw41112step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41112step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41112step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw41116step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41116step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41116step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41117step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw41117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw41118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -1, -2]]
def raw41119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw41119step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw41120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw41123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw41123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41124step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41125step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw41125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41125step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw41125step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41126step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw41126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw41127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw41128step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41128step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-2, 3, -1], ![-3, 0, 3]]
def raw41128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw41128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41129step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw41129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw41129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -1, -2]]
def raw41130step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41131Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw41133step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41134step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw41134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw41136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw41136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw41138step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw41138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw41138step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41139step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw41140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41141step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41142step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw41142step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41142step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]
def raw41142step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41142step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-3, 0, 3]]
def raw41142step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41142step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw41142step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw41143step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41143step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw41143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41143step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw41143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41144step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41144step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41144step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw41144step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41144step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw41144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw41145step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw41145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]
def raw41146step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41146step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41147step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41147step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41148step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41148step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41150step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw41150step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41150step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw41150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41150step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41150step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41151step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41151step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41151step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41151step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41152step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw41156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]
def raw41158step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41158step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw41158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw41159step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw41159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw41159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw41160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw41161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41162step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41162step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![2, 3, -5]]
def raw41162step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41162step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw41162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41163step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41163step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 3, -4], ![1, -1, 0]]
def raw41163step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41163step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw41163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41164step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw41164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41165step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw41165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41165step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw41165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw41166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41166step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]
def raw41166step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41166step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 2, 0], ![-3, 0, 3]]
def raw41166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41166step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw41166step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw41167step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41167step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41167step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41167step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw41169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41169step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]
def raw41169step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41169step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 0, 2], ![-3, 2, 1]]
def raw41169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41169step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw41169step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw41170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw41170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]
def raw41170step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41170step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw41171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw41173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw41173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41173step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41173step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw41174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]
def raw41174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![2, 2, -4]]
def raw41175step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41175step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![2, 2, -4]]
def raw41175step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41175step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw41175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41175step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw41175step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1]]
def raw41176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1]]
def raw41176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1]]
def raw41176step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw41176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw41177step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw41177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41177step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41178step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![2, 3, -5]]
def raw41178step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -3, 5], ![2, 3, -5]]
def raw41178step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw41178step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41179step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41179step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 2, -3], ![1, 1, -2]]
def raw41179step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41179step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 1, 1], ![-3, 1, 2]]
def raw41179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41179step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw41179step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw41180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1]]
def raw41180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw41180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw41181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![3, -1, -2]]
def raw41181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw41181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw41182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw41183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw41184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw41184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41186step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1]]
def raw41188step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![3, -2, -1]]
def raw41188step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw41188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41188step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![3, -1, -2]]
def raw41189step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw41189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw41190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw41191step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![3, -1, -2]]
def raw41193step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41193step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![3, -1, -2]]
def raw41193step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41193step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 3, -1], ![-2, -1, 3]]
def raw41193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41193step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw41193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw41194step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw41194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41195Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41195step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41196Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41196step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41197Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41197step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41198Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41198step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw41198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41199Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41199step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41200Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41201Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41202Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2]]
def raw41202step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![3, -1, -2]]
def raw41202step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -2, 3]]
def raw41202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw41202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41203Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41203step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41204Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41204step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0]]
def raw41204step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41204step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, -2, 0]]
def raw41204step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41204step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw41204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41205Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41205step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1]]
def raw41205step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41206Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41206step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2]]
def raw41206step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41206step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41207Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41207step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1]]
def raw41207step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41208Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41208step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0]]
def raw41208step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41209Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41209step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41210Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41210step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41211Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41212Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41212step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![2, -1, -1]]
def raw41212step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41212step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![2, -1, -1]]
def raw41212step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41212step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-2, -1, 3]]
def raw41212step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41212step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41212step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41213step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2]]
def raw41213step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw41213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41214step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0]]
def raw41214step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw41214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41214step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41214step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41215step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![2, 0, -2]]
def raw41215step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41215step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![2, 0, -2]]
def raw41215step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41215step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw41215step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41215step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw41215step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical322
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw41216step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0]]
def raw41216step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41216step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw41217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1]]
def raw41217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw41218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![3, -1, -2]]
def raw41218step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41218step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw41219step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw41220step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41221Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw41221step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41221step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw41222Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41223Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41223step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41224Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41225Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41226Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1]]
def raw41226step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![3, -2, -1]]
def raw41226step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41226step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41226step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41227Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![3, -1, -2]]
def raw41227step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41227step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41228Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw41228step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41229Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw41229step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41229step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41230Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41231Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![3, -1, -2]]
def raw41231step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![3, -1, -2]]
def raw41231step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41231step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41231step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw41232step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41233step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41233step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41233step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41233step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41234step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41234step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw41234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw41234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41235step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41235step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41235step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41236step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41236step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41236step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41236step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41236step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41237step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41239step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41243step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41243step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw41244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw41246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw41247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw41251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw41254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw41255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw41262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw41262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw41263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw41264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw41265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41266step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw41271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw41275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw41275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw41278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw41278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw41278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw41281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0]]
def raw41281step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw41281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41281step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw41281step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw41282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -2, 2], ![2, 1, -3]]
def raw41289step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw41289step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![1, 1, -2], ![1, -2, 1]]
def raw41290step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw41290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41291step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41291step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw41293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41293step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1]]
def raw41295step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41295step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41298step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, -1, 1], ![2, 1, -3]]
def raw41299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw41299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41299step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![1, 1, -2], ![1, -1, 0]]
def raw41300step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41300step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw41301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![2, 0, -2]]
def raw41302step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![2, 1, -3]]
def raw41303step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41303step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![2, 1, -3]]
def raw41303step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41303step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw41303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41303step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw41303step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw41304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41304step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw41304step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw41304step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw41304step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw41304step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41304step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw41305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw41305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -2, -1]]
def raw41305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41305step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw41307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw41307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw41310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw41313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw41315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw41318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw41318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3], ![2, 1, -3]]
def raw41318step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw41318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41318step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41318step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw41319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw41319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2]]
def raw41319step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw41319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41319step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw41322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw41322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw41323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![3, -1, -2]]
def raw41324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw41330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw41333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw41333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw41333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw41335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw41337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![3, -1, -2]]
def raw41338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![3, -1, -2]]
def raw41338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw41340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0]]
def raw41341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw41341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw41341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![2, -1, -1]]
def raw41342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw41342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -3, 3], ![2, 0, -2]]
def raw41343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical323
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw41349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw41351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw41351step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw41352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2]]
def raw41352step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw41355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw41355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw41356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw41356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw41357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw41357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw41358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw41360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0]]
def raw41360step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw41360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw41361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]
def raw41362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw41368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw41368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw41368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw41368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw41370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw41371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 2, -4]]
def raw41372step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41372step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 2, -3], ![1, -2, 1]]
def raw41373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw41374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw41374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw41378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![2, -1, -1]]
def raw41378step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41378step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw41378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41378step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]
def raw41379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41379step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 2, -4]]
def raw41384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw41384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![1, 2, -3], ![1, -1, 0]]
def raw41385step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41385step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw41385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw41386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw41387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![2, 0, -2]]
def raw41387step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41387step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw41388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw41389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![2, 1, -3]]
def raw41389step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41389step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41389step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![2, 2, -4]]
def raw41390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41390step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 2, -4]]
def raw41390step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41390step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw41390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41390step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw41390step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![3, -2, -1]]
def raw41391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![3, -1, -2]]
def raw41392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw41393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw41394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw41395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw41395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw41396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw41397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![3, -2, -1]]
def raw41400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![3, -2, -1]]
def raw41400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![3, -1, -2]]
def raw41401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw41404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw41406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![3, -1, -2]]
def raw41406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![3, -1, -2]]
def raw41408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw41409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw41411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw41417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw41418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw41419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw41424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw41425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2]]
def raw41426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw41427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw41428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw41429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw41432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![3, -1, -2]]
def raw41432step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41434step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![2, -2, 0]]
def raw41435step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![2, -2, 0]]
def raw41435step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41435step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![2, -1, -1]]
def raw41436step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41437Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -2, 2], ![2, 0, -2]]
def raw41437step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41438Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41438step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41439step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw41442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw41442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw41443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]
def raw41447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41448step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw41452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw41452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw41452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw41453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw41454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 2, -4]]
def raw41455step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -2, 1]]
def raw41456step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw41457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41460step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![2, 3, -5]]
def raw41460step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41461step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41462step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41463step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw41466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![2, -1, -1]]
def raw41466step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw41467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]
def raw41469step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41471Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical324
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw41472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw41472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41473step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw41476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]
def raw41477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw41478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![2, 3, -5]]
def raw41480step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw41481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![2, 0, -2]]
def raw41481step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw41481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41481step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw41481step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw41482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw41483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![2, 1, -3]]
def raw41483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw41483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41483step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw41484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw41485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw41485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 2, -4]]
def raw41486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![2, 2, -4]]
def raw41486step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw41486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw41486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw41487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![2, -1, -1]]
def raw41487step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw41488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw41493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]
def raw41496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw41497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 3, -5]]
def raw41499step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0]]
def raw41500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw41503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![2, 0, -2]]
def raw41503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw41503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw41504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw41506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![2, 1, -3]]
def raw41506step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw41506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41506step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41506step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw41507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]
def raw41507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw41508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw41509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw41509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 2, -4]]
def raw41510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![2, 2, -4]]
def raw41510step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw41510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1]]
def raw41511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1]]
def raw41511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw41511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![2, 3, -5]]
def raw41512step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41512step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 3, -5]]
def raw41512step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41512step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw41512step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![1, 2, -3], ![1, 1, -2]]
def raw41513step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw41513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41514Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 3, 0], ![3, -3, 0]]
def raw41514step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw41514step4Labels : Fin 2 → Fin 2 := ![1, 1]

def raw41514step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw41514step5Labels : Fin 2 → Fin 1 := ![0, 0]

def raw41515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41515Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41515step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41515step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41515step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 3, 0], ![3, -3, 0]]
def raw41515step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw41515step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw41515step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw41515step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw41516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41516Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41516step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41516step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41516step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41517Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41517step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41517step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41517step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41517step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41517step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw41517step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41517step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41517step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41517step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41517step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41518Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41518step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41518step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw41518step3Labels : Fin 2 → Fin 2 := ![1, 1]

def raw41518step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw41518step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw41519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41519Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41519step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41519step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41519step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41519step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41519step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw41519step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw41519step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw41519step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw41520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41520step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41520step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41521Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41521step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41521step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41521step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw41521step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41521step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw41521step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41522Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41522step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41522step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41523Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41523step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41523step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41523step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41523step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41523step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw41523step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41523step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41523step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41523step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41523step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41524Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41525Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41525step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41525step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41525step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41525step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41526Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41527Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41527step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41527step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41527step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41528Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw41528step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw41528step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw41528step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41529Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41529step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41529step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41529step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41529step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41529step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41530Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41531Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41531step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41531step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41531step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41531step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41532Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41532step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41532step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41533Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41533step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41533step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw41533step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41533step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41533step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41533step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41533step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41534Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw41534step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41534step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41534step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41535Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41535step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41535step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41535step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41535step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41535step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41536Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41536step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41536step2Labels : Fin 2 → Fin 2 := ![1, 1]

def raw41536step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41536step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw41537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41537Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41537step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41537step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41537step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41537step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw41537step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41537step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw41538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41538Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41539Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41539step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41539step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41540Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41540step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41540step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41541Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41541step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw41541step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41541step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41541step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41542Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41543Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41543step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41543step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41544Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41545Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41545step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41545step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41545step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41545step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41546Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41547Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41547step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41548Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41548step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41548step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41548step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41548step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41548step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41549Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41549step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41549step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41549step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41549step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41549step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw41549step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41549step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41549step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41549step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41549step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41550Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41550step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41551Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41551step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41551step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41551step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41551step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41551step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41552Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41553Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41553step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41553step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41553step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41553step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41554Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41554step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41555Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41555step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41555step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41555step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41555step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41555step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41556Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41556step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41556step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41557Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41557step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41557step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41557step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41557step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41557step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41558Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41559Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41559step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41559step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41560Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41560step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41561Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41561step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41561step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41562Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41563Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41563step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41563step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41564Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41565Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41565step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41565step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41566Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41567Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41567step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41567step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41568Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41569Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41569step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41569step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41570Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41571Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41571step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41571step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41572Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41573Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41573step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41574Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41575Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41575step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41576Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41577Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41577step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41578Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41578step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41579Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41579step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41580Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41580step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41580step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw41580step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41580step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw41580step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41581Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41581step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41581step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41581step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw41581step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41581step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41581step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41581step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41581step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41582Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41582step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41582step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw41582step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41582step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41582step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41583Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41583step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41583step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41583step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw41583step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41583step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41583step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41583step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41583step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41584Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41584step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41584step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41585Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41585step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41585step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41585step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41585step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41586Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41586step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41586step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41587Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41587step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41587step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41587step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41588Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41588step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41589Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41589step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41589step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41589step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41589step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41589step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41590Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41590step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41590step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41590step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41590step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41590step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41591Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41591step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41591step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41591step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw41591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41591step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41592Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41592step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41592step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41593Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41593step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41593step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41593step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41593step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41593step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41594Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41594step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41595Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41595step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41596Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41596step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41597Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41597step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41597step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41598Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41599Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41599step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41599step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical325
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41600Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41601Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41601step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41601step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41602Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41603Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41603step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41604Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw41604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41604step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41604step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41604step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41605Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41605step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw41605step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41605step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41605step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41605step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw41605step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41605step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41605step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41605step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41605step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41606Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41607Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41607step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41607step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41607step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41608Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41609Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41609step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41609step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41610Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41611Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41611step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41611step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41612Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41613Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41613step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41613step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41614Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41615Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41615step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41615step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41616Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41617Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41617step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41617step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41618Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41619Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41619step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41619step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41620Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41621Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41621step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41621step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41622Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41623Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41623step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41623step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw41623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41624Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41625Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41625step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41625step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41626Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41627Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41627step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41628Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41629Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41629step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41630Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41631Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41631step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41632Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41633Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41633step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41634Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41635Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41635step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41636Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41636step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41636step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41637Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41637step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41637step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw41637step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41637step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41637step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41637step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41638Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41638step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41639Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41639step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41639step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41640Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41641Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41641step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41642Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41642step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41643Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41643step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41644Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41645Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41645step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41646Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41647Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41647step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41648Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41649Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41649step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41650Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41650step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41651Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41651step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41652Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41653Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41653step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41654Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41654step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41655Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41655step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41656Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41656step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41656step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41657Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41657step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41657step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41658Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41659Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41659step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41659step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw41659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw41659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41660Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41660step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41661Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41661step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41661step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41662Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41662step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41662step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41663Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41663step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41663step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41664Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41664step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41665Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41665step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41665step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41666Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41666step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41666step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41667Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41667step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41667step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41668Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41668step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41669Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41669step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41669step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41670Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41670step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41671Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41671step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41672Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41672step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41673Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41673step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41674Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41674step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41674step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41674step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41674step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41674step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41674step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41675Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41675step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw41675step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41675step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41675step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41675step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41676Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41676step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41676step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41676step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw41676step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41676step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw41676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41677Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41677step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41677step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41677step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw41677step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41677step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw41677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41678Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41678step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41678step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41679Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41679step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41679step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41680Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41680step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41680step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41681Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41681step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41681step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41681step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41682Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41682step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41682step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41683Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41683step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41683step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41683step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41684Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41684step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41684step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41684step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41684step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41685Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41685step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw41685step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw41685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41686Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41686step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41686step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41686step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41686step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41686step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41687Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41687step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw41687step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41688Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41688step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41688step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41688step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41688step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41688step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41689Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41689step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw41689step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41689step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41689step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41689step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41690Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41690step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41691Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41691step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41691step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41692Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41692step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41693Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41693step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41694Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41694step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41695Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41695step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41695step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41696Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41696step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41696step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41697Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41697step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41697step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41698Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41698step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41699Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41699step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41700Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41701Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41701step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41701step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41702Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41703Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41704Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw41704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41704step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw41704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41704step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw41704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41705Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41705step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw41705step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41705step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw41705step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41705step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw41705step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41706Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw41706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw41706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw41706step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41706step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw41706step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41707Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41707step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw41707step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw41707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41708Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw41708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw41708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41709Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41709step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw41709step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41710Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41710step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw41710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw41710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41711Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41711step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw41711step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41711step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41712Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw41712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-3, 1, 2]]
def raw41712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw41712step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41712step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw41712step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41713Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41713step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw41713step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw41713step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41714Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41715Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41715step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw41715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41716Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41717Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41717step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw41717step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41717step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41717step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41717step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41718Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw41718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41719Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41719step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41720Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41720step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41721Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41721step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41722Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw41722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41722step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41723Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41723step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41723step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41723step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41724Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw41724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41725Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41725step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41726Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41727Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41727step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw41728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41728Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41729Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41730Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw41730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41731Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41732Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41732step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41733Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41734Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41735Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41735step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41735step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41735step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41735step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41736Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw41736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41737Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41737step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw41737step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41737step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw41737step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41738Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41738step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41739Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41739step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41739step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41739step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41739step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41740Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41741Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41741step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41741step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41742Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41742step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41743Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41743step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw41743step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41743step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41743step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41744Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41745Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41745step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41745step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41745step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41745step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41746Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41747Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41747step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41747step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41747step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41748Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41749Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw41749step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41749step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41749step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41750Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41751Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41751step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41751step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41752Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41752step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41753Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41753step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41753step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41753step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41754Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41755Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41755step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41755step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41756Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41756step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41757Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41757step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41757step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41757step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41757step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41758Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41758step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41759Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw41759step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41759step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41760Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw41760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw41760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41761Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41761step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw41761step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw41761step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41761step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41761step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41761step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41762Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41762step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw41762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw41762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41763Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41763step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw41763step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41763step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41763step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41763step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41763step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41764Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41764step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41765Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41765step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw41765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41765step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41766Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41767Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41767step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41768Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41768step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41769Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41769step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41769step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41769step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41769step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41770Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41771Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41771step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41771step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41771step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41771step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41772Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41772step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41773Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41773step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41773step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41773step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41774Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41775Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41775step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41775step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41776Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41776step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41777Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41777step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41777step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41778Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41779Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41779step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41779step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41780Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41780step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41781Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41781step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41781step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41781step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41782Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41782step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41783Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41783step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41784Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41785Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41785step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41785step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41785step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41785step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41786Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41787Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41788Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41789Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41789step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41789step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41790Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41791Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41791step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41791step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41791step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41792Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41792step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41793Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41793step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw41793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41793step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41793step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41793step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41794Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41795Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41795step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41795step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41795step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41795step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41796Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41797Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw41797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41797step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41797step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41798Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41799Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41799step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41799step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41799step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41800Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41801Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41801step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41801step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw41802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41802Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw41802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]

end MUB6.Certificate.MixedSemantics

end OAI
end


