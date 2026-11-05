-- Prove2me | Definitions.Def_OAIQ106E061
-- name    : OAIQ106E061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T20:05:57.928362+00:00
-- url     : https://prove2.me/theorems/0a28fa90-818e-489b-a451-95e3118a8af6
-- title:
--   Definitions bundle OAIQ106E061 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedData.merged1813`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedMerge_Block56`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedMerge/Block56.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E181` and `OAIQ106E060` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.MUB6.Certificate.MixedData.mergedZero1813_e`; the proofs of `OAI.MUB6.Certificate.MixedData.mergedZero1813_e` and `OAI.MUB6.Certificate.MixedData.mergedZero1814_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E181
import Definitions.Def_OAIQ106E060

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def merged1813 : Integer.Sparse (Fin 3237) := ((((merged1813part0 ++ merged1813part1) ++ (merged1813part2 ++ merged1813part3)) ++ ((merged1813part4 ++ merged1813part5) ++ (merged1813part6 ++ merged1813part7))) ++ (((merged1813part8 ++ merged1813part9) ++ (merged1813part10 ++ merged1813part11)) ++ ((merged1813part12 ++ merged1813part13) ++ (merged1813part14 ++ merged1813part15))))

end MUB6.Certificate.MixedData

end OAI
end


