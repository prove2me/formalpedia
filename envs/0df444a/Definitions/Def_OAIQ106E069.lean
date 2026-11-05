-- Prove2me | Definitions.Def_OAIQ106E069
-- name    : OAIQ106E069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T20:30:37.037859+00:00
-- url     : https://prove2.me/theorems/d3567fe3-efe4-4267-95b0-bf067eda0430
-- title:
--   Definitions bundle OAIQ106E069 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedData.merged2422`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedMerge_Block75`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedMerge/Block75.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E062` and `OAIQ106E068` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E062
import Definitions.Def_OAIQ106E068

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged2422 : Integer.Sparse (Fin 3237) := (((((merged2422part0 ++ merged2422part1) ++ (merged2422part2 ++ merged2422part3)) ++ ((merged2422part4 ++ merged2422part5) ++ (merged2422part6 ++ merged2422part7))) ++ (((merged2422part8 ++ merged2422part9) ++ (merged2422part10 ++ merged2422part11)) ++ ((merged2422part12 ++ merged2422part13) ++ (merged2422part14 ++ merged2422part15)))) ++ ((((merged2422part16 ++ merged2422part17) ++ (merged2422part18 ++ merged2422part19)) ++ ((merged2422part20 ++ merged2422part21) ++ (merged2422part22 ++ merged2422part23))) ++ (((merged2422part24 ++ merged2422part25) ++ (merged2422part26 ++ merged2422part27)) ++ ((merged2422part28 ++ merged2422part29) ++ (merged2422part30 ++ (merged2422part31 ++ merged2422part32))))))

end MUB6.Certificate.MixedData

end OAI
end


