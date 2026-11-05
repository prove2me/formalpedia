-- Prove2me | Definitions.Def_OAIQ106E150
-- name    : OAIQ106E150
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:37:11.726808+00:00
-- url     : https://prove2.me/theorems/041dd8b7-80f3-4cae-993b-2662a64907ee
-- title:
--   Definitions bundle OAIQ106E150 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.MUB6.EqualityPatterns.family2`, `OAI.MUB6.EqualityPatterns.label2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_Moments_SmallPartitions`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Moments/SmallPartitions.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E142` and `OAIQ106E147` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e` and `OAI.MUB6.pair_cross_certificate_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

def label2 (p : Fin 2) (i : Fin 2) : Fin (blocks2 p) :=
  ⟨raw2 p i, by fin_cases p <;> fin_cases i <;> decide⟩

def family2 : Family (Fin 2) (Fin 2) where
  blocks := blocks2
  label := label2
  onto := by decide +kernel
  unique := by decide +kernel

end MUB6.EqualityPatterns

end OAI
end


