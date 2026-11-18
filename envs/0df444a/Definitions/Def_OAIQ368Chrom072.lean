-- Prove2me | Definitions.Def_OAIQ368Chrom072
-- name    : OAIQ368Chrom072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:11:27.67097+00:00
-- url     : https://prove2.me/theorems/16bc83f3-2757-47dd-b864-9948e4f06efd
-- title:
--   Definitions bundle OAIQ368Chrom072 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 instances.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_Cut`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/Cut.lean), [`Chromatic_Shuffle_Split`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/Split.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom017` of this split.
--
--   **Imported by** (directly, in this split): none.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom017

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Cut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality

variable {I : Type*} [Fintype I] [DecidableEq I]

instance instDecidableEqCut (d e : I → ℕ) : DecidableEq (Cut d e) := by unfold Cut; infer_instance

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Split
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ShuffleConvolution
variable {A R : Type*} [Fintype A] [DecidableEq A] [CommSemiring R]

instance instDecidableEqSplit (s : Finset A) : DecidableEq (Split s) := by unfold Split; infer_instance

end ElementaryPositivity.ShuffleConvolution

end

end OAI
end


