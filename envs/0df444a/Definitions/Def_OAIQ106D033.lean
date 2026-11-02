-- Prove2me | Definitions.Def_OAIQ106D033
-- name    : OAIQ106D033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:17:51.115222+00:00
-- url     : https://prove2.me/theorems/d1061fa0-b133-4785-8d40-1df4978a85f8
-- title:
--   Definitions bundle OAIQ106D033 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7166 declarations of OpenAI's Lean: 7166 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw40040step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40040step2`, `OAI.MUB6.Certificate.MixedSemantics.raw40040step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40041`, `OAI.MUB6.Certificate.MixedSemantics.raw40041Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40041step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40041step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40041step1`, `OAI.MUB6.Certificate.MixedSemantics.raw40041step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40041step2`, `OAI.MUB6.Certificate.MixedSemantics.raw40041step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40041step3`, `OAI.MUB6.Certificate.MixedSemantics.raw40041step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40042`, `OAI.MUB6.Certificate.MixedSemantics.raw40042Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40042step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40042step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40042step1`, `OAI.MUB6.Certificate.MixedSemantics.raw40042step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40042step2`, `OAI.MUB6.Certificate.MixedSemantics.raw40042step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40043`, `OAI.MUB6.Certificate.MixedSemantics.raw40043Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step1`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step2`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step3`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step4`, `OAI.MUB6.Certificate.MixedSemantics.raw40043step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40044`, `OAI.MUB6.Certificate.MixedSemantics.raw40044Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40044step0`, `OAI.MUB6.Certificate.MixedSemantics.raw40044step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40044step1`, `OAI.MUB6.Certificate.MixedSemantics.raw40044step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw40044step2` and 7126 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical3`, `MutuallyUnbiased_MixedSemantics_Canonical31`, `MutuallyUnbiased_MixedSemantics_Canonical312`, `MutuallyUnbiased_MixedSemantics_Canonical313`, `MutuallyUnbiased_MixedSemantics_Canonical314`, `MutuallyUnbiased_MixedSemantics_Canonical315`, `MutuallyUnbiased_MixedSemantics_Canonical316`, `MutuallyUnbiased_MixedSemantics_Canonical317`, `MutuallyUnbiased_MixedSemantics_Canonical318`, `MutuallyUnbiased_MixedSemantics_Canonical319`, `MutuallyUnbiased_MixedSemantics_Canonical32`, `MutuallyUnbiased_MixedSemantics_Canonical320`, `MutuallyUnbiased_MixedSemantics_Singletons45`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound349`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound522`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound98`, `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound18`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound19`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound20`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound21`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound22`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound24`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound25`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound27`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound28`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound29`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound30`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound31`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound32`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound33`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound34`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound41`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound42`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound45`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound46`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound47`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound48`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`.
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

def raw400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw400step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw400step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw401 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1]]
def raw401Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw401step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw401step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw402 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0]]
def raw402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw402step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw403 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0]]
def raw403Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw403step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw403step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw404 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw404step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw404step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw404step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw405 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw405Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw405step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw405step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw406 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw406step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw406step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw406step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw407 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
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

def raw4004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw4006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4006step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw4006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4006step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw4006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw4007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4008 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw4008Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4008step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]
def raw4008step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4008step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw4008step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4008step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw4008step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw4009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw4013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw4014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw4015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw4016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw4016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw4017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw4017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![4, -3, -1]]
def raw4021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw4021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw4021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw4023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw4029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw4029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw4029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw4030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![4, -3, -1]]
def raw4031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, -1, 1], ![-1, 3, -2], ![-3, 1, 2]]
def raw4031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4031step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def raw4031step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4036 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4036step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4036step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4036step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4036step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4037 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4037step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4038step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4038step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4039step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4039step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4039step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4039step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4040step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4040step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4040step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4040step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4040step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4044step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4048step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4048step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4058step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4058step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4062 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4062step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4062step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4062step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4063 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4063step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw4063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4064step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4065step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4066step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4066step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4066step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4066step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4066step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40040step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw40040step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40041Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40041step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw40041step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40041step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40041step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40042Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40042step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40042step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40042step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40043Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40043step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40043step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![2, 2, -4]]
def raw40043step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw40043step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw40043step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40044Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40044step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40044step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40044step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![2, 3, -5]]
def raw40044step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40044step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw40044step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40045Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40045step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40045step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40045step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 3, -4], ![1, -1, 0]]
def raw40045step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40045step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw40045step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40046Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40046step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40046step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw40046step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw40047Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw40047step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw40047step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw40047step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw40047step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40048Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40048step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw40048step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]
def raw40048step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 2, 0], ![-3, 0, 3]]
def raw40048step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw40048step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40049Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40049step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw40049step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40049step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40049step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40050Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40050step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw40050step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]
def raw40050step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 0, 2], ![-3, 2, 1]]
def raw40050step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw40050step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40051Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40051step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40051step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw40052Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]
def raw40052step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40052step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40052step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40053Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40053step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw40053step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40053step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40053step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40054Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40054step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40054step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![2, 3, -5]]
def raw40054step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -3, 5], ![2, 3, -5]]
def raw40054step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw40054step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40055Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw40055step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw40055step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40055step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40056Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw40056step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw40056step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40056step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40057Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40057step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40057step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40058Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40058step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40058step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40059Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40059step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40059step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40060Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw40060step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw40060step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40060step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40061Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw40061step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40061step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw40061step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40062Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40062step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40062step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40063Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40063step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1]]
def raw40063step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40063step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40063step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40063step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical313
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40064Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40064step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40064step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40064step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40065Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40065step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40065step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw40065step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40066Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40066step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40066step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40066step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40067Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40067step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40067step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40067step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40068Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40068step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40068step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40068step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40068step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40069Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40069step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40069step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40070Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40070step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40070step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40071Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40071step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw40071step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40071step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40072Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40072step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0]]
def raw40072step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, -2, 0]]
def raw40072step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw40072step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw40072step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40073Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40073step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1]]
def raw40073step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw40073step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40073step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40073step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40074Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40074step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2]]
def raw40074step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw40074step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40074step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw40074step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40075Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40075step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1]]
def raw40075step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40075step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40075step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40075step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40075step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40076Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40076step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0]]
def raw40076step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw40076step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40076step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40077Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40077step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw40077step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw40077step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40078Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40078step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40078step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40078step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40079Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw40079step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw40079step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40080Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40080step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![2, -1, -1]]
def raw40080step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![2, -1, -1]]
def raw40080step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-2, -1, 3]]
def raw40080step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40080step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40081Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40081step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2]]
def raw40081step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw40081step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40081step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40082Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40082step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0]]
def raw40082step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40082step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw40082step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40082step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40082step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40083Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40083step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![2, 0, -2]]
def raw40083step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![2, 0, -2]]
def raw40083step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw40083step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw40083step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40084Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40084step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40084step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40084step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40085Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40085step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40085step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40086Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40086step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40086step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40086step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40087Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40087step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40088Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40088step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40089Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40089step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0]]
def raw40089step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40089step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0]]
def raw40089step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40089step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw40089step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40090Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40090step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40090step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw40090step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40090step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40090step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40091Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40091step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40091step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw40091step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40091step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40092Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40092step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40092step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40093Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40093step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40093step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40093step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40094Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40094step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40094step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40095Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw40095step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40095step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40095step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40096Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40096step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40096step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40097Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40097step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40097step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40098Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40098step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1]]
def raw40098step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![2, -1, -1]]
def raw40098step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw40098step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw40098step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40099Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40099step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2]]
def raw40099step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40099step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40099step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40100Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40100step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -2, 2], ![2, 1, -3]]
def raw40100step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40100step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw40101Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw40101step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![1, 1, -2], ![1, -2, 1]]
def raw40101step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40101step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40102Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40102step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw40102step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40102step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40103Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40103step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40103step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40103step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40104Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40104step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40104step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40105Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40105step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2]]
def raw40105step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![2, 0, -2]]
def raw40105step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw40105step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw40105step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40106Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40106step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![1, 1, -2], ![1, -1, 0]]
def raw40106step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40106step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40106step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40107Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40107step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw40107step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40107step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40108Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40108step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![2, 0, -2]]
def raw40108step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40108step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40108step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40108step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40109Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40109step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![2, 1, -3]]
def raw40109step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![2, 1, -3]]
def raw40109step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw40109step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw40109step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40110Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40110step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw40110step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40110step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw40110step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40110step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw40110step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40110step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw40110step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40111Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40111step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40111step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw40111step1Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40111step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw40111step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40111step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw40111step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40112Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40112step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40112step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40113Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw40113step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40113step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40113step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40114Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw40114step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40114step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40114step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40115Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40115step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40115step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40116Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40116step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40117Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40117step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40117step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40117step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40118Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw40118step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw40118step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40119Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40119step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40119step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40120Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40120step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40121Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40121step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw40121step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40121step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40122Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40122step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40122step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40123Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw40123step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw40123step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40123step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40124Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40124step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40124step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40125Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40125step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40126Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40126step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40126step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40126step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw40126step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40126step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw40126step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40126step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw40126step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40126step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw40126step5Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40127Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40127step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40127step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40127step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40127step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40128Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40128step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40128step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw40128step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40128step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40129Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40129step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40129step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw40129step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40129step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40130Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40130step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40130step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40130step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40130step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40131Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40131step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40131step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40131step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw40131step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40132Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40132step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw40132step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40132step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40133Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40133step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40133step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40134Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40134step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40134step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40135Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40135step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40135step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40136Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw40136step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40136step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40137Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40137step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40137step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40138Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40138step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40138step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40139Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40139step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40140Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40140step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40141Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40141step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40142Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40142step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40142step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40143Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40143step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40143step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40143step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40144Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40144step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40144step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40144step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40145Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40145step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40145step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40146Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40146step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40147Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw40147step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0]]
def raw40147step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40147step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40147step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40148Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw40148step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40148step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40148step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40149Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw40149step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40149step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40149step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40150Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw40150step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40150step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40150step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40151Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2]]
def raw40151step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40151step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40152Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40152step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40152step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40152step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40153Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40153step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40154Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40154step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40155Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40155step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40156Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40156step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40156step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40157Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40157step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40157step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40157step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw40158Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw40158step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40158step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40159Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40159step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40159step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40160Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40160step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40160step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40161Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40161step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40161step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40162Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40162step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40163Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw40163step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0]]
def raw40163step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw40163step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40163step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40163step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40164Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]
def raw40164step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40164step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40164step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40165Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40165step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40165step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40165step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40166Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40166step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40166step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40167Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40167step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40167step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40168Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40168step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40168step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40168step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40169Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40169step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40169step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40170Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40170step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 1, -3]]
def raw40170step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40170step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40171Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40171step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 2, -4]]
def raw40171step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40171step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw40172Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw40172step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 2, -3], ![1, -2, 1]]
def raw40172step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40172step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40173Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40173step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40173step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw40173step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40174Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40174step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40174step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40174step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40175Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40175step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40175step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40176Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw40176step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![2, -1, -1]]
def raw40176step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw40176step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40176step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40177Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]
def raw40177step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40177step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40177step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40178Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40178step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40178step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40178step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40179Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40179step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40179step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40180Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40180step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40180step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40181Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40181step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![2, 0, -2]]
def raw40181step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40181step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40181step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40182Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw40182step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40182step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40182step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40183Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw40183step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40183step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40183step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40184Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40184step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 1, -3]]
def raw40184step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![2, 1, -3]]
def raw40184step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw40184step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw40184step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40185Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40185step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![1, 2, -3], ![1, -1, 0]]
def raw40185step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw40185step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40186Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40186step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw40186step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40186step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40187Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw40187step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![2, 0, -2]]
def raw40187step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40187step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40187step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40188Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40188step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![2, 2, -4]]
def raw40188step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 2, -4]]
def raw40188step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw40188step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw40188step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw40189Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw40189step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40189step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw40190Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40190step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40191Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40191step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical314
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40192Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40192step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw40193Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40193step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40194Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40194step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40195Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw40195step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40195step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw40196Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw40196step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40197Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw40197step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw40197step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40198Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40198step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40198step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40198step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40199Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40199step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40200Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40200step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40201Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40201step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40202Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40202step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40202step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40203Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40203step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40204Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw40204step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0]]
def raw40204step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40204step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw40204step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40204step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40204step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40205Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw40205step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40205step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40206Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]
def raw40206step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40206step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40207Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40207step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40208Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40208step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40209Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40209step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw40210Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40210step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw40210step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40210step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw40211Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40211step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40211step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw40212Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40212step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40212step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2]]
def raw40213Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw40213step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40214Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw40214step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40214step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw40215Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40215step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40216Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40216step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40217Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40217step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40218Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40218step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw40219Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw40219step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40219step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40220Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40220step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40221Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40221step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40222Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![2, -2, 0]]
def raw40222step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![2, -2, 0]]
def raw40222step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40222step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40222step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40223Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![2, -1, -1]]
def raw40223step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40223step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40224Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -2, 2], ![2, 0, -2]]
def raw40224step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40224step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40225Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40225step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40225step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40226Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40226step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40226step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40227Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40227step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40228Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40228step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw40229Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw40229step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40229step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40229step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw40230Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40230step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40230step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40231Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw40231step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]
def raw40231step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40231step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40232Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]
def raw40232step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40232step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40233Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]
def raw40233step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40233step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw40234Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40234step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40234step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40235Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40235step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40236Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40236step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40237Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40237step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40237step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40238Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw40238step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40238step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40239Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 2, -4]]
def raw40239step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40239step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw40240Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -2, 1]]
def raw40240step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40240step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40241Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw40241step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40241step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40242Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40242step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40243Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40243step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40243step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40244Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40244step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 2, -4]]
def raw40244step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40244step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40245Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40245step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![2, 3, -5]]
def raw40245step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40245step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40246Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40246step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40246step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40247Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40247step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40247step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40248Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40248step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40248step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40249Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40249step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40250Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw40250step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![2, -1, -1]]
def raw40250step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40250step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40251Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw40251step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40251step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40252Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40252step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40252step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw40253Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]
def raw40253step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40253step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40253step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40254Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw40254step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![2, 0, -2]]
def raw40254step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40254step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw40254step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40254step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40254step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40255Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw40255step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw40255step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40256Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw40256step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40256step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40256step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40257Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40257step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40257step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40258Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw40258step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40258step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40258step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw40259Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40259step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40259step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw40260Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40260step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40260step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40261Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw40261step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![2, 1, -3]]
def raw40261step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw40261step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40261step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw40261step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40262Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw40262step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40262step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40263Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40263step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40264Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40264step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![2, 2, -4]]
def raw40264step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40264step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![2, 2, -4]]
def raw40264step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40264step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw40264step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40265Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40265step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![2, 3, -5]]
def raw40265step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40265step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40266Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40266step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![1, 3, -4], ![1, -1, 0]]
def raw40266step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40266step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40266step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40267Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw40267step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![2, 0, -2]]
def raw40267step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw40267step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw40267step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40268Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw40268step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40268step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40268step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40269Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw40269step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![2, 1, -3]]
def raw40269step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw40269step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40269step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw40269step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40270Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 2, -4]]
def raw40270step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![2, 2, -4]]
def raw40270step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw40270step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40270step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw40270step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40271Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw40271step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![2, -1, -1]]
def raw40271step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40271step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40272Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw40272step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40272step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40273Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40273step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40273step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40274Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40274step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40275Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw40275step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, 0, -2]]
def raw40275step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw40275step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40276Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40276step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40276step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw40277Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]
def raw40277step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40277step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40277step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40278Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40278step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![2, 2, -4]]
def raw40278step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, 2, -4]]
def raw40278step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40278step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw40278step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40279Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40279step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 3, -5]]
def raw40279step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40279step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40280Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40280step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0]]
def raw40280step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40280step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40280step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40281Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40281step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40281step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw40281step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40282Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40282step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40282step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40283Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw40283step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![2, 0, -2]]
def raw40283step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw40283step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40284Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw40284step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40284step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40284step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40285Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw40285step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![2, 1, -3]]
def raw40285step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40285step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40285step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40285step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40286Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40286step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![2, 3, -5]]
def raw40286step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40286step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 3, -5]]
def raw40286step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40286step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw40286step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40287step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40287step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40287step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40287step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw40287step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40288step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40288step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40288step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40288step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw40288step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40289step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40289step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40289step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40289step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw40289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40290step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40290step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40290step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40290step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw40290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40291step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40291step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40292step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40293step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40293step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40294step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40295step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40296step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40297step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40304step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw40304step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40304step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw40304step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40304step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw40304step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40305step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40305step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40306step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40307step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40308step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40308step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw40314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40322step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw40322step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40322step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40322step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40323step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40324step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40325step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40325step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40325step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40326step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw40326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40327step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw40334step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40334step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw40334step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40334step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw40334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40334step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw40334step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw40335step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw40335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40335step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw40335step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![3, -1, -2]]
def raw40336step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw40336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw40338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw40340step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw40340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40346step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40347step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw40347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40355step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw40355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw40363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40366step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw40366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw40369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40372step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40372step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw40372step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40372step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw40372step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40373step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw40373step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40373step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw40373step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40376step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40377step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40377step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40378step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40378step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw40378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40379step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40380step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw40380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw40385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw40388step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40388step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw40388step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40388step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-3, 3, 0]]
def raw40388step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40388step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw40388step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![3, -2, -1]]
def raw40389step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw40389step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![3, -1, -2]]
def raw40390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw40391step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw40392step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw40393step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw40393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw40395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw40400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw40408step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw40408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40408step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40408step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw40409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw40410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw40415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40424step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw40424step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40424step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw40424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40424step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw40424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40425step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw40425step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw40425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40426step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw40426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw40426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40427step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40428step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40429step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40430step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40431step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40437Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw40437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40438Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40443step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw40443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical316
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40450step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw40450step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw40450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40451step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw40451step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw40451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw40452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40453step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40454step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40455step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40456step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw40456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40457step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40458step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40465step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40465step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40465step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]
def raw40465step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40465step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw40465step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40466step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw40466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40467step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40467step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40468step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40469step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40469step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw40470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw40470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw40470step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw40470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw40471Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw40471step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw40471step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw40472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw40472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw40472step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40472step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw40472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40473step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40474step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40475step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40476step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![3, -2, -1]]
def raw40482step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40482step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw40482step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40482step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 3, -2], ![-3, 0, 3]]
def raw40482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40482step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw40482step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![3, -1, -2]]
def raw40483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-2, 3, -1], ![-3, 0, 3]]
def raw40483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw40483step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw40484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-3, 0, 3]]
def raw40484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40484step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw40484step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw40485step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-3, 0, 3]]
def raw40485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40485step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw40485step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw40486step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 2, 0], ![-3, 0, 3]]
def raw40486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw40486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw40487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw40487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw40488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw40488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw40490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw40490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw40492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]
def raw40492step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 3, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw40492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40492step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw40492step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw40500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw40500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40500step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw40500step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw40501step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40501step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 0, 2], ![-3, 2, 1]]
def raw40501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40501step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw40501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw40507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw40511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw40513step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw40513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw40513step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw40514step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw40514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw40516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40521step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw40521step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw40521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40522step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40522step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40522step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]
def raw40522step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40522step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw40522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40523step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40523step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw40523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40524step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40524step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw40524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40525step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40525step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw40525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40526step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40526step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw40526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40527step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40527step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 1, 1], ![-3, 1, 2]]
def raw40527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw40527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40528step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw40528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40529step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw40529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw40529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw40530step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw40530step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40530step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -3, -2], ![-2, 3, -1], ![-3, 0, 3]]
def raw40530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40530step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw40530step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw40531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw40531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw40531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw40532step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw40532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40532step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw40532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw40534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![3, -1, -2]]
def raw40534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw40534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40534step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw40538step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40538step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw40539step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40539step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40539step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw40543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw40545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw40546step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw40546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw40546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40548step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40548step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw40548step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40548step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-4, 1, 3]]
def raw40548step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40548step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw40548step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40549step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40549step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw40549step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40549step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw40549step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40550step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-4, 1, 3]]
def raw40550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw40550step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw40551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40551step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw40551step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1]]
def raw40552step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw40552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40552step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40552step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![3, -1, -2]]
def raw40553step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-2, -1, 3]]
def raw40553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw40554step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw40555step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw40556step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw40557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40557step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1]]
def raw40563step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40563step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![3, -2, -1]]
def raw40563step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40563step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-2, -1, 3]]
def raw40563step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40563step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40563step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![3, -1, -2]]
def raw40564step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-2, -1, 3]]
def raw40564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40564step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw40565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw40566step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![3, -1, -2]]
def raw40569step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40569step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![3, -1, -2]]
def raw40569step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40569step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -2, 3], ![-2, 3, -1]]
def raw40569step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40569step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw40569step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw40570step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw40570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40570step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40571step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40571step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 3, -1], ![2, -3, 1]]
def raw40571step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -1, 3], ![2, 1, -3]]
def raw40571step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40572step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40572step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![2, -2, 0]]
def raw40572step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40572step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw40572step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40573step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40573step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40573step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40573step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw40573step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40574step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40574step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40574step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40574step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40574step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw40574step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40574step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw40574step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40575step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40575step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40575step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40575step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]
def raw40575step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical317
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40576step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw40576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40577step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw40577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40578step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw40578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40580step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw40580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40585step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40585step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw40586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw40586step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw40588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw40588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40593step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw40601step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw40614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40618step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw40624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw40624step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw40624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40624step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw40625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw40625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw40626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw40632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40633step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw40637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![3, -1, -2]]
def raw40637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw40637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40637step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw40641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw40641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw40641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40643step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![2, -3, 1]]
def raw40643step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40643step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw40643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40643step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw40643step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw40644step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw40644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40645step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw40645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw40647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw40647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw40647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw40647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40648step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw40650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw40652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40656step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40656step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40656step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40656step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw40656step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40656step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw40656step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40657step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40657step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40657step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40657step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw40657step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40657step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw40657step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40658step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw40658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40659step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw40659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw40660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40660step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw40660step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40661step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40661step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw40662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40664step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]
def raw40664step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40664step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw40664step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40664step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw40664step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40665step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40665step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40666step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw40666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40667step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40667step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40668step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw40677step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40677step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40684step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw40685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw40685step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40685step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw40686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![3, -1, -2]]
def raw40687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40688step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw40690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw40698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw40704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw40708step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40710step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw40718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw40718step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw40718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40718step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![3, -1, -2]]
def raw40719step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw40719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw40720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40721step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw40722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw40728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw40729step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw40730step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![3, -1, -2]]
def raw40735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![3, -1, -2]]
def raw40735step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw40735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40735step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw40736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw40737step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw40737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw40739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw40739step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw40739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw40742step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw40743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![2, -1, -1]]
def raw40744step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw40744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40745step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw40745step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw40745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40746step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw40746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40747step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -3, 1]]
def raw40747step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40747step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, -3, 1]]
def raw40747step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40747step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw40747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40747step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw40747step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40748step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0]]
def raw40748step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw40748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw40748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40749step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -2, 2], ![2, -1, -1]]
def raw40749step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40750step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -3, 3], ![2, 0, -2]]
def raw40750step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw40751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw40751step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40751step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40751step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40752step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40752step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw40752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40753step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40755step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw40756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40758step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw40762step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw40762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw40762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40763step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw40769step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40769step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40771step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40771step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40771step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40773step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40773step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40773step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]
def raw40773step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40773step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw40773step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40774step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40774step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40774step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 2, -3], ![1, -3, 2]]
def raw40774step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40774step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40774step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40775step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40776step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40778step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw40778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40778step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40779step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40779step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw40780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw40780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![3, -3, 0]]
def raw40783step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40783step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw40783step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40783step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw40783step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40783step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw40783step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![3, -2, -1]]
def raw40784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw40784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![3, -1, -2]]
def raw40785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -2, 3], ![-2, 2, 0]]
def raw40785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40785step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw40785step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40786step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw40786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40787step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]
def raw40788step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw40789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40793step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2901 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


