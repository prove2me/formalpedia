-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T09:25:01.704898+00:00
-- url     : https://prove2.me/theorems/823ec92e-e9b4-4910-a117-33d30bc3c121
-- title:
--   Exists Res Eq Of Unit In Chart
-- statement:
--   Definitions and structural lemmas for Exists Res Eq Of Unit In Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsResEqOfUnitInChart.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ker_fin
import Theorems.Thm_GlobalTheory_SqZero_IsAway_surj_fin
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
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
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply


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
section Der
variable {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
def addDer (φ : B →ₐ[R] A) (D : B →ₗ[R] A) (hD : ∀ b b', D (b * b') = φ b * D b' + φ b' * D b)
    (h0 : ∀ b b', D b * D b' = 0) : B →ₐ[R] A :=
  AlgHom.ofLinearMap (φ.toLinearMap + D)
    (by
      have := hD 1 1
      simp only [mul_one, map_one, one_mul, left_eq_add] at this
      simp [this])
    (fun b b' => by
      simp only [LinearMap.add_apply, AlgHom.toLinearMap_apply, map_mul, hD]
      linear_combination - h0 b b')
def addDers {κ : Type} [Fintype κ] (τ : κ → Derivation R B B) (φ : B →ₐ[R] A) (t : κ → A)
    (ht : ∀ i j, t i * t j = 0) : B →ₐ[R] A :=
  addDer φ
    { toFun := fun b => ∑ i, φ (τ i b) * t i
      map_add' := fun b b' => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r b => by simp [Finset.smul_sum] }
    (fun b b' => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun b b' => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        rw [mul_mul_mul_comm, ht, mul_zero])
end Der
section Dual
variable {S S' S'' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S'']
abbrev fstS (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S] :
    DualNumber S →ₐ[R] S := TrivSqZeroExt.fstHom R S S
abbrev inlS (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S] :
    S →ₐ[R] DualNumber S := TrivSqZeroExt.inlAlgHom R S S
def dualMap (ρ : S →ₐ[R] S') : DualNumber S →ₐ[R] DualNumber S' :=
  dualTo ((inlS R S').comp ρ) (inr 1) (TrivSqZeroExt.inr_mul_inr _ _ _)
def dualScale (R : Type) [CommRing R] {S : Type} [CommRing S] [Algebra R S] (s : S) :
    DualNumber S →ₐ[R] DualNumber S :=
  dualTo (inlS R S) (inr s) (TrivSqZeroExt.inr_mul_inr _ _ _)
@[simp] theorem fst_dualMap (ρ : S →ₐ[R] S') (a : DualNumber S) :
    (dualMap ρ a).fst = ρ a.fst := by
  simp [dualMap, dualTo_apply]
@[simp] theorem snd_dualMap (ρ : S →ₐ[R] S') (a : DualNumber S) :
    (dualMap ρ a).snd = ρ a.snd := by
  simp [dualMap, dualTo_apply]
@[simp] theorem fst_dualScale (s : S) (a : DualNumber S) : (dualScale R s a).fst = a.fst := by
  simp [dualScale, dualTo_apply]
@[simp] theorem snd_dualScale (s : S) (a : DualNumber S) : (dualScale R s a).snd = a.snd * s := by
  simp [dualScale, dualTo_apply, mul_comm]
theorem fstS_comp_dualMap (ρ : S →ₐ[R] S') :
    (fstS R S').comp (dualMap ρ) = ρ.comp (fstS R S) := AlgHom.ext fun a => by simp [fstS]
theorem fstS_comp_dualScale (s : S) : (fstS R S).comp (dualScale R s) = fstS R S := AlgHom.ext fun a => by simp [fstS]
theorem IsAway.dualMap {ρ : S →ₐ[R] S'} {g : S} (h : IsAway ρ g) :
    IsAway (dualMap ρ) (inlS R S g) := by
  have hi : ∀ x : S, GlobalTheory.SqZero.dualMap ρ (inlS R S x) = inlS R S' (ρ x) := fun x =>
    TrivSqZeroExt.ext (by simp) (by simp)
  rw [isAway_iff, hi]
  refine ⟨h.unit.map (inlS R S'), fun z => ?_, fun a ha => ?_⟩
  · obtain ⟨N, a, ha⟩ := h.surj_fin ![z.fst, z.snd]
    have h0 := ha 0
    have h1 := ha 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨N, inlS R S (a 0) + inr (a 1), ?_⟩
    rw [← map_pow]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [h0]
    · simp [h1, mul_comm]
  · have e0 : ρ a.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst ha
    have e1 : ρ a.snd = 0 := by simpa using congrArg TrivSqZeroExt.snd ha
    obtain ⟨N, hN⟩ := h.ker_fin (a := ![a.fst, a.snd]) (fun i => by fin_cases i <;> simp [e0, e1])
    have h0 := hN 0
    have h1 := hN 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨N, ?_⟩
    rw [← map_pow]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [h0]
    · simp [h1]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
def IsTanOver (w : sp (R₀ := R) (DualNumber S) ⟶ G) : Prop := spMap (fstS R S) ≫ w = 1
abbrev res (ρ : S →ₐ[R] S') (w : sp (R₀ := R) (DualNumber S) ⟶ G) :
    sp (R₀ := R) (DualNumber S') ⟶ G := spMap (dualMap ρ) ≫ w
abbrev scl (s : S) (w : sp (R₀ := R) (DualNumber S) ⟶ G) :
    sp (R₀ := R) (DualNumber S) ⟶ G := spMap (dualScale R s) ≫ w
theorem IsTanOver.res {w : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) (ρ : S →ₐ[R] S') :
    IsTanOver (res ρ w) := by
  unfold IsTanOver at hw ⊢
  dsimp only [GlobalTheory.SqZero.res]
  rw [← Category.assoc, spMap_comp, fstS_comp_dualMap, ← spMap_comp, Category.assoc, hw, comp_one']
theorem IsTanOver.scl {w : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) (s : S) :
    IsTanOver (scl s w) := by
  unfold IsTanOver at hw ⊢
  dsimp only [GlobalTheory.SqZero.scl]
  rw [← Category.assoc, spMap_comp, fstS_comp_dualScale, hw]
variable [Smooth G.hom] {ρ : S →ₐ[R] S'} {g : S}
end Dual
end GlobalTheory.SqZero


