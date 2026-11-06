-- Prove2me | Definitions.Def_OAIQ106E163
-- name    : OAIQ106E163
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T03:27:49.322054+00:00
-- url     : https://prove2.me/theorems/cb469a59-03dd-48b9-bfee-d0a7bca1d443
-- title:
--   Definitions bundle OAIQ106E163 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.MUB6.TaoCertificate.combined439`, `OAI.MUB6.TaoCertificate.combined44`, `OAI.MUB6.TaoCertificate.combined445`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_TaoCertificate_Merge5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge5.lean), [`MutuallyUnbiased_TaoCertificate_Merge54`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge54.lean), [`MutuallyUnbiased_TaoCertificate_Merge55`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge55.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E159` and `OAIQ106E162` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.TaoCertificate.combined414_zero_e` and `OAI.MUB6.TaoCertificate.combined455_zero_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E159
import Definitions.Def_OAIQ106E162

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined44 : Sparse := combined44_part0 ++ combined44_part1

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined439 : Sparse := combined439_part0 ++ combined439_part1 ++ combined439_part2 ++ combined439_part3 ++ combined439_part4 ++ combined439_part5 ++ combined439_part6 ++ combined439_part7 ++ combined439_part8 ++ combined439_part9 ++ combined439_part10 ++ combined439_part11 ++ combined439_part12 ++ combined439_part13 ++ combined439_part14 ++ combined439_part15 ++ combined439_part16 ++ combined439_part17 ++ combined439_part18 ++ combined439_part19

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined445 : Sparse := combined445_part0 ++ combined445_part1 ++ combined445_part2 ++ combined445_part3 ++ combined445_part4 ++ combined445_part5 ++ combined445_part6 ++ combined445_part7 ++ combined445_part8 ++ combined445_part9 ++ combined445_part10 ++ combined445_part11 ++ combined445_part12 ++ combined445_part13 ++ combined445_part14 ++ combined445_part15 ++ combined445_part16 ++ combined445_part17 ++ combined445_part18 ++ combined445_part19

end MUB6.TaoCertificate

end OAI
end


