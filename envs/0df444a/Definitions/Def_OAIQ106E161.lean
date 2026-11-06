-- Prove2me | Definitions.Def_OAIQ106E161
-- name    : OAIQ106E161
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T03:34:39.820962+00:00
-- url     : https://prove2.me/theorems/b134cd16-4bfa-4d21-8bf6-9725ea404e1e
-- title:
--   Definitions bundle OAIQ106E161 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.TaoCertificate.combined396`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_TaoCertificate_Merge49`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge49.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E158` and `OAIQ106E160` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.MUB6.TaoCertificate.combined396_zero_e`; the proofs of `OAI.MUB6.TaoCertificate.combined396_zero_e` and `OAI.MUB6.TaoCertificate.combined414_zero_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E158
import Definitions.Def_OAIQ106E160

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined396 : Sparse := combined396_part0 ++ combined396_part1 ++ combined396_part2 ++ combined396_part3 ++ combined396_part4 ++ combined396_part5 ++ combined396_part6 ++ combined396_part7 ++ combined396_part8 ++ combined396_part9 ++ combined396_part10 ++ combined396_part11 ++ combined396_part12 ++ combined396_part13 ++ combined396_part14 ++ combined396_part15

end MUB6.TaoCertificate

end OAI
end


