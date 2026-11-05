-- Prove2me | Definitions.Def_OAIQ106E064
-- name    : OAIQ106E064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T22:47:57.862406+00:00
-- url     : https://prove2.me/theorems/cbe7e64c-5fd5-493d-aaae-ab67f24a13d0
-- title:
--   Definitions bundle OAIQ106E064 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedData.merged1964`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedMerge_Block61`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedMerge/Block61.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E182` and `OAIQ106E063` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.MUB6.Certificate.MixedData.mergedZero1964_e`; the proofs of `OAI.MUB6.Certificate.MixedData.mergedZero1964_e` and `OAI.MUB6.Certificate.MixedData.mergedZero1965_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E182
import Definitions.Def_OAIQ106E063

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged1964 : Integer.Sparse (Fin 3237) := (((merged1964part0 ++ (merged1964part1 ++ merged1964part2)) ++ (merged1964part3 ++ (merged1964part4 ++ merged1964part5))) ++ ((merged1964part6 ++ (merged1964part7 ++ merged1964part8)) ++ ((merged1964part9 ++ merged1964part10) ++ (merged1964part11 ++ merged1964part12))))

end MUB6.Certificate.MixedData

end OAI
end


