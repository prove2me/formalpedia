-- Prove2me | Definitions.Def_OAIQ368Chrom034
-- name    : OAIQ368Chrom034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:35:42.455819+00:00
-- url     : https://prove2.me/theorems/e410aa53-028d-4685-9c27-60a58927e2fe
-- title:
--   Definitions bundle OAIQ368Chrom034 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 definition and 1 theorem. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.globalSignOperator`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_TensorMiddleEnd`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TensorMiddleEnd.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom030` and `OAIQ368Chrom033` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom035`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom030
import Definitions.Def_OAIQ368Chrom033

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorMiddleEnd
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def globalSignOperator (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) :
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  TensorProduct.lift (directSumBilinear (unitalComponent a c η hc θ)
    (unitalComponent a c η hc θ) _ (fun k l=>TensorProduct.curry
      (((-1:ℚ)^eulerForm a k.1.val l.1.val) • TensorProduct.map
        (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) k)
        (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) l))))

lemma globalSignOperator_tmul_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (k l : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) (y : unitalComponent a c η hc θ l) :
    globalSignOperator a c η hc θ
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
        DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y)=
      ((-1:ℚ)^eulerForm a k.1.val l.1.val) •
        (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]
          DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l y) := by
  rw [globalSignOperator,TensorProduct.lift.tmul,directSumBilinear_lof]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end


