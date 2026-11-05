-- Prove2me | Definitions.Def_OAIQ106E133
-- name    : OAIQ106E133
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:26:08.064625+00:00
-- url     : https://prove2.me/theorems/44f1a91a-5756-4c1c-a4d0-3dc2e5da8b01
-- title:
--   Definitions bundle OAIQ106E133 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedTargetSemantics.numericRawPolynomial`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedTargets_ReductionFinalArithmetic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionFinalArithmetic.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E043` and `OAIQ106E071` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E071

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionFinalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def numericRawPolynomial : Integer.Sparse (Fin 3237) := ((((MixedData.targetRow0 ++ MixedData.targetRow1) ++ (MixedData.targetRow2 ++ (MixedData.targetRow3 ++ MixedData.targetRow4))) ++ ((MixedData.targetRow5 ++ (MixedData.targetRow6 ++ MixedData.targetRow7)) ++ (MixedData.targetRow8 ++ (MixedData.targetRow9 ++ MixedData.targetRow10)))) ++ (((MixedData.targetRow11 ++ (MixedData.targetRow12 ++ MixedData.targetRow13)) ++ (MixedData.targetRow14 ++ (MixedData.targetRow15 ++ MixedData.targetRow16))) ++ ((MixedData.targetRow17 ++ (MixedData.targetRow18 ++ MixedData.targetRow19)) ++ (MixedData.targetRow20 ++ (MixedData.targetRow21 ++ MixedData.targetRow22)))))

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


