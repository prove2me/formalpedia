-- Prove2me | Definitions.Def_OAIQ106E078
-- name    : OAIQ106E078
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T20:46:19.207842+00:00
-- url     : https://prove2.me/theorems/84c662c4-7cfc-4223-8541-f9f1acd1c451
-- title:
--   Definitions bundle OAIQ106E078 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedData.targetRows`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedData_Targets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Targets.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E184` and `OAIQ106E071` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e`, `OAI.MUB6.Certificate.MixedData.mergedEval2452_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`; the proofs of `OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e`, `OAI.MUB6.Certificate.MixedData.mergedEval2452_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e` and `OAI.MUB6.family_size_le_five_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E071

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Targets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def targetRows (i : Fin 29) : Integer.Sparse (Fin 3237) :=
  (#[targetRow0, targetRow1, targetRow2, targetRow3, targetRow4, targetRow5, targetRow6, targetRow7, targetRow8, targetRow9, targetRow10, targetRow11, targetRow12, targetRow13, targetRow14, targetRow15, targetRow16, targetRow17, targetRow18, targetRow19, targetRow20, targetRow21, targetRow22, targetRow23, targetRow24, targetRow25, targetRow26, targetRow27, targetRow28])[i.val]!

end MUB6.Certificate.MixedData

end OAI
end


