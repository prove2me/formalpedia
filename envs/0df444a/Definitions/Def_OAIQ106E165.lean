-- Prove2me | Definitions.Def_OAIQ106E165
-- name    : OAIQ106E165
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T03:34:28.970905+00:00
-- url     : https://prove2.me/theorems/7ccc8248-415b-43df-a780-acdc7bcbbb6c
-- title:
--   Definitions bundle OAIQ106E165 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.TaoCertificate.combined459`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_TaoCertificate_Merge57`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge57.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E162` and `OAIQ106E164` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.MUB6.TaoCertificate.combined474_zero_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E162
import Definitions.Def_OAIQ106E164

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined459 : Sparse := combined459_part0 ++ combined459_part1 ++ combined459_part2 ++ combined459_part3 ++ combined459_part4 ++ combined459_part5 ++ combined459_part6 ++ combined459_part7 ++ combined459_part8 ++ combined459_part9 ++ combined459_part10 ++ combined459_part11 ++ combined459_part12 ++ combined459_part13 ++ combined459_part14 ++ combined459_part15 ++ combined459_part16 ++ combined459_part17 ++ combined459_part18

end MUB6.TaoCertificate

end OAI
end


