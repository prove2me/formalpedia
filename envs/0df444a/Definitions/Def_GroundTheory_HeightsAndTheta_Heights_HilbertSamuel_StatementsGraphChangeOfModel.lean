-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphChangeOfModel
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphChangeOfModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:53.506117+00:00
-- url     : https://prove2.me/theorems/0079c4bf-1aa8-472a-8077-f56bc18158f8
-- title:
--   Statements Graph Change Of Model
-- statement:
--   Definitions and structural lemmas for Statements Graph Change Of Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsGraphChangeOfModel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
section Objects
variable {K : Type} {ι : K → Type} {K₂ : Type} {ι₂ : K₂ → Type}
def formApply (g : (Σ k, ι₂ k) → MRing ι) (z : (Σ k, ι k) → ℂ) : (Σ k, ι₂ k) → ℂ :=
  fun q => eval z (map (Int.castRingHom ℂ) (g q))
variable [Fintype K] [∀ k, Fintype (ι k)]
end Objects
def GraphChangeOfModel.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι) (δ : K₂ → K → ℕ)
      (G : GenFibre inrV (graphIdeal P g))
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι ι₂) (Sum.inr : K₂ → K ⊕ K₂)))
      (L : Fin d → HermLine ι₂) (L₁ : Fin d → HermLine ι),
      IsArithVar P d → (∀ q, IsMultiHomog (g q) (δ q.1)) → IsBasePtFree P g →
      IsArithVar (imageZ inrV (graphIdeal P g)) d → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L₁ j)) →
      (∀ j k, (L₁ j).a k = ∑ k₂, (L j).a k₂ * (δ k₂ k : ℤ)) →
      (∀ j, ∀ z ∈ mcPts P, (L₁ j).h z = (L j).h (formApply g z)) →
      I K ι P d L₁ = (J (fibreIdeal Sum.inr G) 0 Fin.elim0 : ℝ) * I K₂ ι₂ (imageZ inrV (graphIdeal P g)) d L
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.HilbertSamuel


