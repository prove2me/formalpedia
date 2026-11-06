-- Prove2me | Definitions.Def_OAIQ106E169
-- name    : OAIQ106E169
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T03:33:26.244411+00:00
-- url     : https://prove2.me/theorems/592ecd34-1156-47c9-abd8-84c9b42c7cde
-- title:
--   Definitions bundle OAIQ106E169 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.MUB6.TaoCertificate.targetCombined1`, `OAI.MUB6.TaoCertificate.targetCombined2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_TaoCertificate_TargetMerge1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/TargetMerge1.lean), [`MutuallyUnbiased_TaoCertificate_TargetMerge2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/TargetMerge2.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E164` and `OAIQ106E167` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.MUB6.complete_family_square_not_hadamard_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E164
import Definitions.Def_OAIQ106E167

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def targetCombined1 : Sparse := targetCombined1_part0 ++ targetCombined1_part1 ++ targetCombined1_part2 ++ targetCombined1_part3

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def targetCombined2 : Sparse := targetCombined2_part0 ++ targetCombined2_part1 ++ targetCombined2_part2 ++ targetCombined2_part3 ++ targetCombined2_part4

end MUB6.TaoCertificate

end OAI
end


