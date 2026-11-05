-- Prove2me | Definitions.Def_OAIQ106E111
-- name    : OAIQ106E111
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:19:30.137176+00:00
-- url     : https://prove2.me/theorems/3c5b8c5f-b05a-4749-a85e-2d0639d7d5a6
-- title:
--   Definitions bundle OAIQ106E111 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7541 declarations of OpenAI's Lean: 7541 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw39812step0`, `OAI.MUB6.Certificate.MixedSemantics.raw39812step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39813`, `OAI.MUB6.Certificate.MixedSemantics.raw39813Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39813step0`, `OAI.MUB6.Certificate.MixedSemantics.raw39813step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39814`, `OAI.MUB6.Certificate.MixedSemantics.raw39814Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39814step0`, `OAI.MUB6.Certificate.MixedSemantics.raw39814step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39815`, `OAI.MUB6.Certificate.MixedSemantics.raw39815Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39815step0`, `OAI.MUB6.Certificate.MixedSemantics.raw39815step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39815step1`, `OAI.MUB6.Certificate.MixedSemantics.raw39815step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39815step2`, `OAI.MUB6.Certificate.MixedSemantics.raw39815step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39816`, `OAI.MUB6.Certificate.MixedSemantics.raw39816Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39816step0`, `OAI.MUB6.Certificate.MixedSemantics.raw39816step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39816step1`, `OAI.MUB6.Certificate.MixedSemantics.raw39816step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39816step2`, `OAI.MUB6.Certificate.MixedSemantics.raw39816step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39817`, `OAI.MUB6.Certificate.MixedSemantics.raw39817Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39817step0`, `OAI.MUB6.Certificate.MixedSemantics.raw39817step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39817step1`, `OAI.MUB6.Certificate.MixedSemantics.raw39817step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39818`, `OAI.MUB6.Certificate.MixedSemantics.raw39818Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39818step0`, `OAI.MUB6.Certificate.MixedSemantics.raw39818step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39818step1`, `OAI.MUB6.Certificate.MixedSemantics.raw39818step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw39819`, `OAI.MUB6.Certificate.MixedSemantics.raw39819Labels` and 7501 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical3.lean), [`MutuallyUnbiased_MixedSemantics_Canonical31`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical31.lean), [`MutuallyUnbiased_MixedSemantics_Canonical311`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical311.lean), [`MutuallyUnbiased_MixedSemantics_Canonical312`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical312.lean), [`MutuallyUnbiased_MixedSemantics_Canonical313`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical313.lean), [`MutuallyUnbiased_MixedSemantics_Canonical314`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical314.lean), [`MutuallyUnbiased_MixedSemantics_Canonical315`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical315.lean), [`MutuallyUnbiased_MixedSemantics_Canonical316`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical316.lean), [`MutuallyUnbiased_MixedSemantics_Canonical317`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical317.lean), [`MutuallyUnbiased_MixedSemantics_Canonical318`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical318.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound11_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound13_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound14_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound15_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound16_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound17_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound19_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound20_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound22_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound24_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound25_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound27_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound28_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound29_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound30_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound31_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound32_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound33_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound34_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound35_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound41_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound42_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`.
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

def raw3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw3step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw3step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw4 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw39Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw39step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw39step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]

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

def raw398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw398step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw398step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw399 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw399Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw399step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw399step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw400 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1]]
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

def raw3981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3981step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw3981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3981step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3981step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3981step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3982step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3982step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3982step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3985step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw3986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3987step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw3991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3992step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw3992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw3992step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3992step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw3992step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3993step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw3993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3993step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3993step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3993step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw3994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw3995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3996step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw3996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3996step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3996step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3997step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw3997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw3997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![4, -3, -1]]
def raw4001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw4001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw4001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw4003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39812step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39813Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39813step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39814Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39814step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39815Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39815step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39815step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39815step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39816Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39816step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39816step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39816step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39817Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39817step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39817step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39818Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39818step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39818step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39819Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39819step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39819step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39820Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39820step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39820step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39821Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39821step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39822Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39822step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39823Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw39823step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw39823step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw39823step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw39823step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39824Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw39824step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39824step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39824step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39825Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw39825step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39825step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39826Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw39826step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw39826step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39827Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39827step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39828Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39828step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39829Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw39829step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39829step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39829step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39830Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39830step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39831Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39831step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39832Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw39832step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39833Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw39833step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw39833step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39834Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39834step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39834step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39834step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39835Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39835step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39835step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39836Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw39836step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39836step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39837Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39837step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39838Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39838step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39839Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39839step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39840Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw39840step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39840step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39841Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw39841step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw39841step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39842Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39842step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39843Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39843step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39844Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39844step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -3, 2], ![2, 3, -5]]
def raw39844step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw39844step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39845Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39845step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39845step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39846Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39846step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39846step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39847Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39847step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39847step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39848Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39848step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39848step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39849Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39849step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39850Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw39850step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39850step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39851Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw39851step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39851step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39852Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw39852step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39852step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39853Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39853step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39854Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39854step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39854step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39855Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39855step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39855step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39856Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39856step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39856step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39857Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39857step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39857step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39857step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39858Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw39858step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39858step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39859Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39859step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39860Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39860step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39861Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39861step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39861step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39862Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw39862step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39862step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39863Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39863step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39863step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39864Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw39864step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39864step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39865Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39865step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39866Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39866step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39867Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39867step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw39867step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39867step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39868Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39868step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39868step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39868step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39869Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39869step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw39869step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39869step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39870Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39870step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39870step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39871Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw39871step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39871step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39872Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39872step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39872step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39873Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw39873step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw39873step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw39873step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39874Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw39874step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39874step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39875Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39875step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw39875step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39875step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39876Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39876step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![2, -3, 1]]
def raw39876step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]
def raw39876step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw39876step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39876step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39877Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39877step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![2, -2, 0]]
def raw39877step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39877step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39877step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39878Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39878step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![2, -1, -1]]
def raw39878step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39878step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39879Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39879step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![2, 0, -2]]
def raw39879step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw39879step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39880Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39880step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39880step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39880step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw39881Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw39881step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39881step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39882Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39882step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39882step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39883Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39883step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39883step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39884Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39884step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39884step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39885Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39885step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw39885step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw39885step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39886Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39886step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39887Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39887step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39888Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39888step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39889Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw39889step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![2, -3, 1]]
def raw39889step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39889step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39890Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39890step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39890step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39890step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39891Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39891step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39891step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39892Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39892step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39893Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39893step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39894Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw39894step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39894step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39895Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39895step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw39895step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39895step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39896Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39896step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw39896step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw39896step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39896step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39897Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39897step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]
def raw39897step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39897step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39898Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39898step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 1, -2], ![1, -3, 2]]
def raw39898step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw39898step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39899Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39899step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39899step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39899step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39900Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39900step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39900step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39900step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39901Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39901step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39901step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39902Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39902step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39902step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39903Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39903step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39903step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39904Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39904step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39904step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39905Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39905step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39905step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39906Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39906step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39906step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39906step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39907Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39907step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw39907step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39907step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39908Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39908step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39909Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39909step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw39910Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39910step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39910step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39911Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw39911step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39911step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39912Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw39912step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39912step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39912step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw39913Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw39913step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw39913step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39913step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39914Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39914step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39915Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39915step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39916Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39916step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39916step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39917Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39917step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw39917step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39917step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39918Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39918step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 2, -3], ![1, -3, 2]]
def raw39918step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39918step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39919Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39919step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39919step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39920Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39920step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39920step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39921Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39921step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39921step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39922Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39922step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39922step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39923Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39923step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39923step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39923step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39924Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39924step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw39924step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw39924step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39925Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39925step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw39926Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw39926step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw39926step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 2, -4]]
def raw39926step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw39926step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw39927Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw39927step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw39927step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 3, -5]]
def raw39927step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw39927step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw39928Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw39928step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw39928step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]
def raw39928step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39928step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw39929Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw39929step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw39929step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39929step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw39930Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw39930step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw39930step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39930step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw39931Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw39931step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw39931step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39931step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw39932Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw39932step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw39932step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39932step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39933Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39933step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39933step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39933step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39934Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39934step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39934step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw39934step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39934step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw39935Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw39935step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw39935step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw39935step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

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

def raw39936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw39936Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw39936step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw39936step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw39936step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw39936step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw39937Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw39937step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39937step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw39938Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw39938step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39938step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw39939Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw39939step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39939step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw39940Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw39940step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39940step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw39941Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39941step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39942Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39942step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39942step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw39942step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39942step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39943Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39943step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39943step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw39943step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39943step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39944Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39944step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw39944step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39944step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39945Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39945step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39945step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39945step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39946Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39946step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39946step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39946step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39947Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39947step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39947step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39948Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39948step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39948step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39949Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39949step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39949step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39949step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39949step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39950Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39950step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39950step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39950step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39950step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39951Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39951step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw39951step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw39951step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39952Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39952step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39952step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw39952step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39953Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39953step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39953step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39953step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39954Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39954step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39954step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39954step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39955Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39955step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39955step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw39955step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39956Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39956step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39956step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39957Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39957step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39957step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39958Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39958step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39958step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39958step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39959Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39959step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39959step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw39959step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39960Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39960step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39960step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw39960step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39961Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39961step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39961step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39961step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39962Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39962step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39962step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39963Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39963step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw39963step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39964Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw39964step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39964step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39965Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw39965step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw39965step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39966Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw39966step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39966step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39967Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39967step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39968Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39968step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39968step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39969Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39969step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39969step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39970Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39970step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw39970step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39970step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39971Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39971step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39971step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39971step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39972Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw39972step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw39972step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39973Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39973step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39973step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39974Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39974step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39974step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39975Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39975step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39975step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39976Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw39976step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39976step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39977Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39977step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw39977step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39977step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39978Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw39978step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39978step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39979Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39979step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39980Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw39980step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39981Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39981step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39981step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39981step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39982Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39982step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39982step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw39982step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39983Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39983step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39983step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39984Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw39984step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39984step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39985Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39985step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39985step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39985step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39986Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39986step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![2, -2, 0]]
def raw39986step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]
def raw39986step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39986step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39987Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39987step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![2, -1, -1]]
def raw39987step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39987step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39988Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39988step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![2, 0, -2]]
def raw39988step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw39988step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39989Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39989step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39989step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39989step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39990Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39990step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39990step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw39990step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39991Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39991step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39991step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39992Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39992step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39992step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39993Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39993step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw39993step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39994Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39994step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39995Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw39995step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw39995step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39995step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39995step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39996Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw39996step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39996step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39996step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39997Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39997step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39997step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39997step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39998Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39998step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]
def raw39998step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw39998step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw39999Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw39999step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]
def raw39999step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39999step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39999step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40000Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40000step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40000step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40000step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40000step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40001Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40001step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40001step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40001step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40002Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40002step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40002step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw40003Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw40003step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw40003step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40003step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40004Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40004step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40004step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40005Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40005step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40005step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40006Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40006step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![2, 2, -4]]
def raw40006step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40006step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40007Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40007step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40007step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40007step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40008Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40008step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw40008step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw40008step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40009Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40009step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40009step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 3, -5]]
def raw40009step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw40009step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw40010Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw40010step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw40010step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 3, -4], ![1, -2, 1]]
def raw40010step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw40010step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40011Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40011step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40011step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 2, -3], ![1, -1, 0]]
def raw40011step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw40011step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40012Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40012step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40012step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40012step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40013Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40013step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40013step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw40013step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40014Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40014step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40014step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw40014step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw40014step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40015Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40015step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40015step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw40015step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40016Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40016step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40016step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40017Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40017step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]
def raw40017step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw40017step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40017step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40018Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40018step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40018step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40018step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40019Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40019step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40019step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw40019step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw40019step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40020Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw40020step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40020step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40020step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40021Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40021step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40021step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw40021step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40022Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw40022step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw40022step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40022step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40023Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw40023step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40023step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40024Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw40024step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw40024step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40024step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40025Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw40025step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw40025step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40026Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40026step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40026step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw40026step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40027Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40027step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw40027step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw40027step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw40027step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40028Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40028step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40028step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw40028step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw40028step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40029Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40029step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40029step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40029step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40030Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40030step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40030step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40030step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40031Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40031step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40031step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40031step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40032Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40032step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40032step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40033Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40033step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw40033step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw40033step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw40033step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw40033step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40034Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40034step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw40034step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40034step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40034step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40035Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40035step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw40035step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40035step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40035step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40036Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40036step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40036step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40036step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40037Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40037step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40037step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40038Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw40038step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40038step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40038step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40039Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40039step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw40039step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw40039step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw40039step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw40039step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40040Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40040step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]
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

def raw40793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


