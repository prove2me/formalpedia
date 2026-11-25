-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:32.89184+00:00
-- url     : https://prove2.me/theorems/da441a84-76cd-42a1-92ad-1c4beef62ef0
-- title:
--   Finrank Hom Complex
-- statement:
--   Definitions and structural lemmas for Finrank Hom Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
def sesq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (hermForm Hm)
    (fun _ _ _ => by simp [hermForm]) (fun _ _ _ => by simp [hermForm])
    (fun _ _ _ => by simp [hermForm, Matrix.mulVec_add]) (fun _ _ _ => by simp [hermForm, Matrix.mulVec_smul])
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
def imForm (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) : LinearMap.BilinForm ℝ W :=
  LinearMap.mk₂ ℝ (fun x y => (S x y).im) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r x]; simp) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r y, LinearMap.map_smulₛₗ]; simp)
@[simp] theorem imForm_apply (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x y : W) : imForm S x y = (S x y).im := rfl
def reForm (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) : LinearMap.BilinForm ℝ W :=
  LinearMap.mk₂ ℝ (fun x y => (S x y).re) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r x]; simp) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r y, LinearMap.map_smulₛₗ]; simp)
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}
section
variable (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
  (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) {b : W →ₗ[ℝ] W} (hb : ∀ w, b w ∈ R)
  (hb' : ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im)
variable {O : Type} [CommRing O] [StarRing O] {ρ : O →+* Module.End ℂ W}
  (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w)) (hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R)
end
section Hom
variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
end Hom
end GlobalTheory.OfPeriod


