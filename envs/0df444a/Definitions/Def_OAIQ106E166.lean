-- Prove2me | Definitions.Def_OAIQ106E166
-- name    : OAIQ106E166
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T03:29:05.96021+00:00
-- url     : https://prove2.me/theorems/7b1b5f13-57e2-4c06-9e3a-265d6e640d99
-- title:
--   Definitions bundle OAIQ106E166 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.MUB6.TaoCertificate.combined53`, `OAI.MUB6.TaoCertificate.combined81`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_TaoCertificate_Merge10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge10.lean), [`MutuallyUnbiased_TaoCertificate_Merge6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge6.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E159` and `OAIQ106E164` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.TaoCertificate.combined396_zero_e` and `OAI.MUB6.TaoCertificate.combined455_zero_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E159
import Definitions.Def_OAIQ106E164

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined53 : Sparse := combined53_part0 ++ combined53_part1 ++ combined53_part2

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined81 : Sparse := combined81_part0 ++ combined81_part1 ++ combined81_part2

end MUB6.TaoCertificate

end OAI
end


