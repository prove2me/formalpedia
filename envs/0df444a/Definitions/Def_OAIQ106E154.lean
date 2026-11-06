-- Prove2me | Definitions.Def_OAIQ106E154
-- name    : OAIQ106E154
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T02:57:26.739171+00:00
-- url     : https://prove2.me/theorems/e04fdcc9-d84f-461e-a130-b5ff3b2201d2
-- title:
--   Definitions bundle OAIQ106E154 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.MUB6.PairCertificateIdentity`, `OAI.MUB6.TaoArithmetic.OrderTwoValues`, `OAI.MUB6.pairL`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_PairMoments_PairCharges`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairMoments/PairCharges.lean), [`MutuallyUnbiased_Tao_TaoTarget`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Tao/TaoTarget.lean).
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106E140` and `OAIQ106E147` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.MUB6.pair_cross_certificate_e`; the proofs of `OAI.MUB6.complete_family_square_not_hadamard_e`, `OAI.MUB6.family_size_le_five_e`, `OAI.MUB6.fourier_and_family_bound` and `OAI.MUB6.pair_cross_certificate_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMoments_PairCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

def pairL (H : CMatrix) : ℂ :=
  -g H pairW + ∑ j, pairCoefficient j * g H (pairA j) * g H (pairW - pairA j)

def PairCertificateIdentity (H : CMatrix) (q : Charge) : Prop :=
  3 * pairAverage H (fun K => Complex.normSq (pairL K)) +
    pairAverage H (fun K => Complex.normSq (g K alpha * g K q)) = 0

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

def OrderTwoValues (f : Charge → ℂ) : Prop :=
  ∀ a, Balanced a → order a = 2 → f a = -(g tao a) / 5

end MUB6.TaoArithmetic

end

end OAI
end


