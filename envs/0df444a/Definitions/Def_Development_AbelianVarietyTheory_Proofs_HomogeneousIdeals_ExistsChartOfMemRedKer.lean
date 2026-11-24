-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:37.890071+00:00
-- url     : https://prove2.me/theorems/e8093df9-8076-4256-8c31-c60668ad230f
-- title:
--   Exists Chart Of Mem Red Ker
-- statement:
--   Definitions and structural lemmas for Exists Chart Of Mem Red Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsChartOfMemRedKer.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
namespace GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
section Maps
variable {S S' A A' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
def dualTo (f : S →ₐ[R] A) (t : A) (ht : t * t = 0) : DualNumber S →ₐ[R] A :=
  DualNumber.lift ⟨(f, t), ht, fun _ => Commute.all _ _⟩
theorem dualTo_apply (f : S →ₐ[R] A) (t : A) (ht : t * t = 0) (a : DualNumber S) :
    dualTo f t ht a = f a.fst + f a.snd * t := rfl
def epsTo (R : Type) [CommRing R] {A : Type} [CommRing A] [Algebra R A] (t : A) (ht : t * t = 0) :
    DualNumber R →ₐ[R] A := dualTo (Algebra.ofId R A) t ht
@[simp] theorem epsTo_eps (t : A) (ht : t * t = 0) : epsTo R t ht DualNumber.eps = t := by
  simp [epsTo, dualTo_apply]
def vecTo {n : ℕ} (α : S →ₐ[R] A) (c : Fin n → A) (hc : ∀ i j, c i * c j = 0) :
    TrivSqZeroExt S (Fin n → S) →ₐ[R] A :=
  TrivSqZeroExt.lift α
    { toFun := fun m => ∑ i, α (m i) * c i
      map_add' := fun m m' => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r m => by simp [Finset.smul_sum] }
    (fun x y => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        rw [mul_mul_mul_comm, hc, mul_zero])
    (fun r x => by simp [Finset.mul_sum, mul_assoc])
    (fun r x => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, op_smul_eq_mul, map_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring)
end Maps
section Group
variable (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {A A' A₀ : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  [CommRing A₀] [Algebra R A₀]
def pointsMap (φ : A →ₐ[R] A') : (sp A ⟶ G) →* (sp A' ⟶ G) where
  toFun y := spMap φ ≫ y
  map_one' := MonObj.comp_one _
  map_mul' := MonObj.comp_mul _
def redKer (J : Ideal A) : Subgroup (sp (R₀ := R) A ⟶ G) := (pointsMap G (Ideal.Quotient.mkₐ R J)).ker
variable {G}
variable (G A) in

def UnitInChart : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (j : sp B ⟶ G) (u : B →ₐ[R] A),
    IsOpenImmersion j.left ∧ spMap u ≫ j = 1
variable [IsCommMonObj G] {n : ℕ}
def lieExp (v : Fin n → (epsR R ⟶ G)) (c : Fin n → A) (hc : ∀ i, c i * c i = 0) : sp A ⟶ G :=
  ∏ i, spMap (epsTo R (c i) (hc i)) ≫ v i
variable {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
include hv
end Group
end GlobalTheory.SqZero


