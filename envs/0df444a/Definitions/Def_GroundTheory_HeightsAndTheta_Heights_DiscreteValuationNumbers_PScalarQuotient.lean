-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:50.097543+00:00
-- url     : https://prove2.me/theorems/12143f96-61c2-42ca-9ab6-134afae22a90
-- title:
--   PScalar Quotient
-- statement:
--   Definitions and structural lemmas for PScalar Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace ScalarQuotient
section ClassNumbers
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
theorem classNum_add {σ : Type*} (cls : σ → K → ℤ) (H₁ H₂ : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (H₁ + H₂) Q W = classNum cls H₁ Q W + classNum cls H₂ Q W := by
  classical
  unfold classNum
  have ext : ∀ (H : MvPolynomial σ ℤ) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      ∑ μ ∈ H.support, H.coeff μ * vNumL W (classList cls μ ++ Q) =
        ∑ μ ∈ s, H.coeff μ * vNumL W (classList cls μ ++ Q) := by
    intro H s hs
    refine Finset.sum_subset hs fun μ _ hμ => ?_
    rw [MvPolynomial.mem_support_iff, not_not] at hμ
    rw [hμ, zero_mul]
  rw [ext (H₁ + H₂) (H₁.support ∪ H₂.support) support_add,
    ext H₁ (H₁.support ∪ H₂.support) Finset.subset_union_left,
    ext H₂ (H₁.support ∪ H₂.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_add, add_mul]
def classNumHom {σ : Type*} (cls : σ → K → ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    MvPolynomial σ ℤ →+ ℤ where
  toFun H := classNum cls H Q W
  map_zero' := by simp [classNum]
  map_add' H₁ H₂ := classNum_add cls H₁ H₂ Q W
end ClassNumbers
section Divisors
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [DecidableEq K]
end Divisors
end ScalarQuotient
end
end GroundTheory.Heights₂.Heights.NumbersDVR


