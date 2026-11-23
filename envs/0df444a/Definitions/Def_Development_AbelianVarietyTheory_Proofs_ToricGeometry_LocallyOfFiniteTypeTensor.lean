-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:20.965843+00:00
-- url     : https://prove2.me/theorems/b2a7e337-0703-45da-af5c-870bcab0e33f
-- title:
--   Locally Of Finite Type Tensor
-- statement:
--   Definitions and structural lemmas for Locally Of Finite Type Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_GlobalTheory_top_le_preimage_comp
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
namespace ThetaModelGroup
variable {X Y : Over (Sp ℂ)}
def RegOn (U : Y.left.Opens) (s : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ) : Prop :=
  ∃ ρ : Γ(Y.left, U), ∀ y' : 𝟙_ (Over (Sp ℂ)) ⟶ Y, ⊤ ≤ y'.left ⁻¹ᵁ U → valAt' y'.left U ρ = s y'
def RegAt (y : 𝟙_ (Over (Sp ℂ)) ⟶ Y) (s : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ) : Prop :=
  ∃ U : Y.left.Opens, ⊤ ≤ y.left ⁻¹ᵁ U ∧ RegOn U s
theorem RegAt.comp {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y} (p : Y ⟶ X) {s : (𝟙_ (Over (Sp ℂ)) ⟶ X) → ℂ}
    (h : RegAt (y ≫ p) s) : RegAt y (fun y' => s (y' ≫ p)) := by
  obtain ⟨U, hU, ρ, hρ⟩ := h
  refine ⟨p.left ⁻¹ᵁ U, (top_le_preimage_comp _ _ _).1 hU, (p.left.app U).hom ρ, fun y' hy' => ?_⟩
  exact (valAt'_comp _ _ _ _).trans (hρ (y' ≫ p) ((top_le_preimage_comp _ _ _).2 hy'))
def PointCriterion : Prop :=
  ∀ (X Y : Over (Sp ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y
def IsLevel {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (f : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
    eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z
end ThetaModelGroup
end GlobalTheory


