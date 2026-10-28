-- Prove2me | Definitions.Def_OAIQ15Sf011
-- name    : OAIQ15Sf011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:29:46.829338+00:00
-- url     : https://prove2.me/theorems/61751672-0a90-416f-82e4-d4e1b9c5e624
-- title:
--   Definitions bundle OAIQ15Sf011 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 4 definitions and 6 theorems. The definitions and types are `OAI.KaplanskyConsequences.Regular.canonicalTrace`, `OAI.KaplanskyConsequences.Regular.tensorCoeff`, `OAI.KaplanskyConsequences.Regular.tensorGroup`, `OAI.KaplanskyConsequences.SpectralKernel.val`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: [`Kaplansky_Quotient_NullIdeal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/NullIdeal.lean), [`Kaplansky_Regular_ReducedPolynomials`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedPolynomials.lean), [`Kaplansky_Regular_ReducedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedTensor.lean), [`Kaplansky_Regular_ReducedTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedTrace.lean).
--
--   **Imports.** It imports the published bundle `Def_KaplanskyStableFiniteness`; the bundles `OAIQ15Sf002` and `OAIQ15Sf008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ15Sf012`; the proofs of `OAI.KaplanskyConsequences.Regular.algebra_F2_simple`, `OAI.KaplanskyConsequences.Regular.polynomial_average_small`, `OAI.KaplanskyConsequences.Regular.polynomial_dense_zero`, `OAI.KaplanskyConsequences.Regular.tensor_two_isometries_of_small_tuple` and `OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf002
import Definitions.Def_OAIQ15Sf008

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_NullIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped Matrix CStarAlgebra ComplexOrder
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

namespace SpectralKernel
variable (d : CuntzDimensionState A)

abbrev val {n : ℕ} (a : Mat A n) : ℝ := d.signedValue a

lemma val_of_nonneg {n : ℕ} {a : Mat A n} (ha : 0 ≤ a) :
    val d a = d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ :=
  d.signedValue_of_nonneg ha

@[simp] lemma val_zero (n : ℕ) : val d (0 : Mat A n) = 0 := d.signedValue_zero n

lemma val_nonneg {n : ℕ} {a : Mat A n} (ha : 0 ≤ a) : 0 ≤ val d a := by
  rw [val_of_nonneg d ha]
  exact d.spectralValue_nonneg _

lemma val_mono {n : ℕ} {a b : Mat A n} (ha : 0 ≤ a) (hab : a ≤ b) :
    val d a ≤ val d b := by
  rw [val_of_nonneg d ha, val_of_nonneg d (ha.trans hab)]
  exact d.spectralValue_mono_positive ha (ha.trans hab) hab

end SpectralKernel
end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped InnerProductSpace ComplexOrder BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2200] Complex.partialOrder
variable {G : Type*}

variable [Group G]

lemma coefficient_tracial (S T : Algebra G) : coefficient (S*T) = coefficient (T*S) := by
  have he (X Y : Algebra G) : coefficient (X*Y) = ∑' g, X.val (delta 1) g⁻¹ * Y.val (delta 1) g := by
    rw [coefficient,← inner_delta]
    change inner ℂ (delta 1) (X.val (Y.val (delta 1))) = _
    rw [← ContinuousLinearMap.adjoint_inner_left,lp.inner_eq_tsum]
    apply tsum_congr; intro g
    change inner ℂ ((star X).val (delta 1) g) (Y.val (delta 1) g) = _
    rw [algebra_star_delta]
    simp [RCLike.inner_apply,mul_comm]
  rw [he,he]
  simpa [mul_comm] using ((Equiv.inv G).tsum_eq (fun g => S.val (delta 1) g⁻¹ * T.val (delta 1) g)).symm

def canonicalTrace : TracialState (Algebra G) where
  functional := PositiveLinearMap.mk₀
    { toFun := coefficient
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (fun T hT => by
      obtain ⟨X,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
      change 0 ≤ coefficient (star X*X)
      rw [coefficient_square]
      rw [inner_self_eq_norm_sq_to_K]
      positivity)
  normalized := by
    change coefficient 1 = 1
    simp [coefficient,delta_apply]
  tracial := coefficient_tracial


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

@[simp] lemma coefficient_polynomial (c : G →₀ ℂ) : coefficient (polynomial c) = c 1 := by
  change (canonicalTrace.functional) (polynomial c) = _
  simp only [polynomial,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
  change (∑ g ∈ c.support, c g • coefficient (generator g)) = _
  simp only [coefficient_generator,smul_eq_mul,mul_ite,mul_one,mul_zero]
  simp [eq_comm]


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def tensorCoeff (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) : tensorAlgebra (G:=G) ρ :=
  ⟨diagonal (ρ a),StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩))⟩
def tensorGroup (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (g : G) : tensorAlgebra (G:=G) ρ :=
  ⟨left g,StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨g,rfl⟩))⟩


end KaplanskyConsequences.Regular

end

end OAI
end


