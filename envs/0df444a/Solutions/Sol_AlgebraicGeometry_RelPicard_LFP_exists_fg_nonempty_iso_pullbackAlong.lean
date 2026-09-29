-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/10301363-0d50-50e9-a8ce-4c47690bdade

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_FGSubalgebra
import Definitions.Def_AlgebraicGeometry_FGSubalgebraTensorStage
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_Module_IsDirectLimit_exists_invertible_linearEquiv_baseChange
import Theorems.Thm_Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat
import Theorems.Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Spec Scheme Scheme.Hom.naturality Scheme.Modules Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap FGSubalgebra RelPicard.LFP.stageHom"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle LFP.stageHom RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom"
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

section ActR

variable (k : Type*) [CommRing k] {Γ : Type*} [CommRing Γ] [Algebra k Γ]
  (A' : Type*) [CommRing A'] [Algebra k A']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]

noncomputable def actR (s : Γ) : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P :=
  (DistribSMul.toLinearMap k P s).baseChange A'

@[scoped simp] theorem actR_tmul (s : Γ) (a : A') (m : P) :
    actR k A' s (a ⊗ₜ[k] m) = a ⊗ₜ[k] (s • m) := by
  simp [actR, DistribSMul.toLinearMap_apply]

theorem actR_one : actR k A' (1 : Γ) = (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P) := by
  ext m; simp

theorem actR_mul (s t : Γ) : actR k A' (P := P) (s * t) = actR k A' s ∘ₗ actR k A' t := by
  ext m; simp [mul_smul]

theorem actR_add (s t : Γ) : actR k A' (P := P) (s + t) = actR k A' s + actR k A' t := by
  ext m; simp [add_smul, tmul_add]

theorem rTensor_actR {A'' : Type*} [CommRing A''] [Algebra k A''] (h : A' →ₐ[k] A'') (s : Γ)
    (x : A' ⊗[k] P) :
    h.toLinearMap.rTensor P (actR k A' s x) = actR k A'' s (h.toLinearMap.rTensor P x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp [hx, hy]

theorem rTensor_smul' {A'' : Type*} [CommRing A''] [Algebra k A''] (h : A' →ₐ[k] A'')
    {Q : Type*} [AddCommGroup Q] [Module k Q] (a : A') (x : A' ⊗[k] Q) :
    h.toLinearMap.rTensor Q (a • x) = h a • h.toLinearMap.rTensor Q x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

theorem tmul_eq_smul_one_tmul {Q : Type*} [AddCommGroup Q] [Module k Q] (a : A') (m : Q) :
    a ⊗ₜ[k] m = a • ((1 : A') ⊗ₜ[k] m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end ActR

section Intertwines

variable {k : Type*} [CommRing k] {Γ Γ' Γ'' : Type*} [CommRing Γ] [Algebra k Γ] [CommRing Γ'] [Algebra k Γ']
  [CommRing Γ''] [Algebra k Γ'']
  {A' : Type*} [CommRing A'] [Algebra k A']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {Q : Type*} [AddCommGroup Q] [Module Γ' Q] [Module k Q] [IsScalarTower k Γ' Q]
  {N : Type*} [AddCommGroup N] [Module Γ'' N] [Module k N] [IsScalarTower k Γ'' N]

def Intertwines (σ : Γ → Γ') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) : Prop :=
  ∀ (s : Γ) (x : A' ⊗[k] P), f (actR k A' s x) = actR k A' (σ s) (f x)

theorem Intertwines.comp {σ : Γ → Γ'} {σ' : Γ' → Γ''} {f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q}
    {g : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] N} (hf : Intertwines σ f) (hg : Intertwines σ' g) :
    Intertwines (σ' ∘ σ) (g ∘ₗ f) := fun s x => by
  simp [LinearMap.comp_apply, hf s x, hg (σ s)]

theorem Intertwines.id : Intertwines (_root_.id : Γ → Γ) (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P) :=
  fun _ _ => rfl

theorem Intertwines.symm {e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q} {σ : Γ ≃ Γ'}
    (he : Intertwines σ (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)) :
    Intertwines σ.symm (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P) := fun s y => by
  apply e.injective
  change e (e.symm (actR k A' s y)) = e (actR k A' (σ.symm s) (e.symm y))
  rw [LinearEquiv.apply_symm_apply]
  have := he (σ.symm s) (e.symm y)
  simp only [LinearEquiv.coe_coe, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem Intertwines.baseChange (σ : Γ → Γ') (r : P →ₗ[k] Q) (hr : ∀ (s : Γ) (m : P), r (s • m) = σ s • r m) :
    Intertwines σ (r.baseChange A') := fun s x => by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [hr]
  | add x y hx hy => simp only [map_add, hx, hy]

end Intertwines

section Ext

variable {k : Type*} [CommRing k] {Γ : Type*} [CommRing Γ] [Algebra k Γ]
  {A' : Type*} [CommRing A'] [Algebra k A']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {N : Type*} [AddCommGroup N] [Module A' N]

theorem linearMap_ext_of_span (F G : A' ⊗[k] P →ₗ[A'] N) (T : Γ → N → N)
    (hF : ∀ (s : Γ) (x : A' ⊗[k] P), F (actR k A' s x) = T s (F x))
    (hG : ∀ (s : Γ) (x : A' ⊗[k] P), G (actR k A' s x) = T s (G x))
    (gens : Set P) (hgens : Submodule.span Γ gens = ⊤)
    (h : ∀ m ∈ gens, F ((1 : A') ⊗ₜ[k] m) = G ((1 : A') ⊗ₜ[k] m)) : F = G := by

  let S : Submodule Γ P :=
    { carrier := {m | F ((1 : A') ⊗ₜ[k] m) = G ((1 : A') ⊗ₜ[k] m)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, tmul_add, map_add] at ha hb ⊢; rw [ha, hb]
      zero_mem' := by simp
      smul_mem' := fun s m hm => by
        simp only [Set.mem_setOf_eq] at hm ⊢
        rw [← actR_tmul k A', hF, hG, hm] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hgens, Submodule.span_le]; exact h
  have h1 : ∀ m : P, F ((1 : A') ⊗ₜ[k] m) = G ((1 : A') ⊗ₜ[k] m) := fun m => by
    have : m ∈ S := by rw [hS]; trivial
    exact this
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [tmul_eq_smul_one_tmul k A', map_smul, map_smul, h1]
  | add x y hx hy => simp only [map_add, hx, hy]

end Ext

section Push

variable {k : Type*} [CommRing k] {Γ Γ' : Type*} [CommRing Γ] [Algebra k Γ] [CommRing Γ'] [Algebra k Γ']
  {A' A'' : Type*} [CommRing A'] [Algebra k A'] [CommRing A''] [Algebra k A'']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {Q : Type*} [AddCommGroup Q] [Module Γ' Q] [Module k Q] [IsScalarTower k Γ' Q]
  {N : Type*} [AddCommGroup N] [Module k N]

private noncomputable def _root_.AlgebraicGeometry.RelPicard.LFP.push (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) :
    A'' ⊗[k] P →ₗ[A''] A'' ⊗[k] Q :=
  LinearMap.liftBaseChange A''
    ((h.toLinearMap.rTensor Q) ∘ₗ (f.restrictScalars k) ∘ₗ (TensorProduct.mk k A' P 1))

p2m_export "AlgebraicGeometry.RelPicard.LFP" "push"
@[scoped simp] theorem push_tmul (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (a : A'') (m : P) :
    push h f (a ⊗ₜ[k] m) = a • h.toLinearMap.rTensor Q (f ((1 : A') ⊗ₜ[k] m)) := by
  simp [push, LinearMap.liftBaseChange_tmul]

theorem push_rTensor (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (x : A' ⊗[k] P) :
    push h f (h.toLinearMap.rTensor P x) = h.toLinearMap.rTensor Q (f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, push_tmul, ← rTensor_smul' k A' h,
      ← map_smul, ← tmul_eq_smul_one_tmul k A']
  | add x y hx hy => simp only [map_add, hx, hy]

theorem push_id (h : A' →ₐ[k] A'') :
    push h (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P) = LinearMap.id := by
  ext m; simp

theorem push_comp (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)
    (g : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] N) :
    push h (g ∘ₗ f) = push h g ∘ₗ push h f := by
  ext m
  simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, push_tmul, one_smul]
  rw [push_rTensor]

theorem Intertwines.push {σ : Γ → Γ'} (h : A' →ₐ[k] A'') {f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q}
    (hf : Intertwines σ f) : Intertwines σ (push h f) := fun s x => by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [actR_tmul, push_tmul, push_tmul, ← actR_tmul k A', hf, rTensor_actR, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_baseChange (h : A' →ₐ[k] A'') {M M' : Type*} [AddCommGroup M] [Module k M] [AddCommGroup M']
    [Module k M'] (r : M →ₗ[k] M') (x : A' ⊗[k] M) :
    h.toLinearMap.rTensor M' (r.baseChange A' x) = r.baseChange A'' (h.toLinearMap.rTensor M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem push_square (h : A' →ₐ[k] A'') {P' : Type*} [AddCommGroup P'] [Module k P'] {Q' : Type*} [AddCommGroup Q']
    [Module k Q'] (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P') (g : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] Q')
    (r : P →ₗ[k] Q) (r' : P' →ₗ[k] Q') (hsq : ∀ x, g (r.baseChange A' x) = r'.baseChange A' (f x))
    (y : A'' ⊗[k] P) : push h g (r.baseChange A'' y) = r'.baseChange A'' (push h f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, push_tmul, push_tmul, map_smul, ← rTensor_baseChange, ← hsq,
      LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_span_range_of_algEquiv {Γ'' : Type*} [CommRing Γ''] [Algebra A' Γ'']
    (e : A' ⊗[k] Γ ≃ₐ[A'] Γ'') (φ : Γ → Γ'') (he : ∀ s, e ((1 : A') ⊗ₜ[k] s) = φ s) (y : Γ'') :
    y ∈ Submodule.span A' (Set.range φ) := by
  obtain ⟨x, rfl⟩ := e.surjective y
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul a s =>
    rw [tmul_eq_smul_one_tmul k A' a s, map_smul, he]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨s, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

noncomputable def pushEquiv (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q) :
    A'' ⊗[k] P ≃ₗ[A''] A'' ⊗[k] Q :=
  LinearEquiv.ofLinear (push h (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q))
    (push h (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P))
    (by rw [← push_comp]; simp [push_id])
    (by rw [← push_comp]; simp [push_id])

@[scoped simp] theorem pushEquiv_apply (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q) (x : A'' ⊗[k] P) :
    pushEquiv h e x = push h (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) x := rfl

@[scoped simp] theorem pushEquiv_symm_apply (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q)
    (x : A'' ⊗[k] Q) :
    (pushEquiv h e).symm x = push h (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P) x := rfl

theorem coe_pushEquiv (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q) :
    (pushEquiv h e : A'' ⊗[k] P →ₗ[A''] A'' ⊗[k] Q) = push h (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) := rfl

end Push

section Orient

variable (k : Type*) [CommRing k] (Γ : Type*) [CommRing Γ] [Algebra k Γ]
  (A' : Type*) [CommRing A'] [Algebra k A']
  (P : Type*) [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]

noncomputable def orient : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[k] A' ⊗[k] P :=
  ((TensorProduct.comm Γ (Γ ⊗[k] A') P).restrictScalars k) ≪≫ₗ
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange k Γ Γ P A').restrictScalars k) ≪≫ₗ
  (TensorProduct.comm k P A')

@[scoped simp] theorem orient_tmul (γ : Γ) (a : A') (m : P) :
    orient k Γ A' P ((γ ⊗ₜ[k] a) ⊗ₜ[Γ] m) = a ⊗ₜ[k] (γ • m) := by
  simp [orient]

@[scoped simp] theorem orient_symm_tmul (a : A') (m : P) :
    (orient k Γ A' P).symm (a ⊗ₜ[k] m) = ((1 : Γ) ⊗ₜ[k] a) ⊗ₜ[Γ] m := by
  rw [LinearEquiv.symm_apply_eq, orient_tmul, one_smul]

theorem orient_smul (γ : Γ) (a : A') (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A' P ((γ ⊗ₜ[k] a) • x) = a • actR k A' γ (orient k Γ A' P x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul γ' a' =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, orient_tmul,
        orient_tmul, actR_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_smul]
    | add x y hx hy => simp only [smul_add, add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem orient_smul_left (a : A') (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A' P (((1 : Γ) ⊗ₜ[k] a) • x) = a • orient k Γ A' P x := by
  rw [orient_smul, actR_one, LinearMap.id_apply]

theorem orient_smul_right (γ : Γ) (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A' P ((γ ⊗ₜ[k] (1 : A')) • x) = actR k A' γ (orient k Γ A' P x) := by
  rw [orient_smul, one_smul]

theorem orient_symm_smul (a : A') (y : A' ⊗[k] P) :
    (orient k Γ A' P).symm (a • y) = ((1 : Γ) ⊗ₜ[k] a) • (orient k Γ A' P).symm y := by
  rw [LinearEquiv.symm_apply_eq, orient_smul_left, LinearEquiv.apply_symm_apply]

theorem orient_symm_actR (γ : Γ) (y : A' ⊗[k] P) :
    (orient k Γ A' P).symm (actR k A' γ y) = (γ ⊗ₜ[k] (1 : A')) • (orient k Γ A' P).symm y := by
  rw [LinearEquiv.symm_apply_eq, orient_smul_right, LinearEquiv.apply_symm_apply]

theorem orient_rTensor_map {A'' : Type*} [CommRing A''] [Algebra k A''] (h : A' →ₐ[k] A'')
    (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A'' P ((Algebra.TensorProduct.map (AlgHom.id Γ Γ) h).toLinearMap.rTensor P x) =
      h.toLinearMap.rTensor P (orient k Γ A' P x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul γ a => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {k Γ A' P}
variable {Q : Type*} [AddCommGroup Q] [Module Γ Q] [Module k Q] [IsScalarTower k Γ Q]

noncomputable def fromOrient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q where
  toFun y := orient k Γ A' Q (f ((orient k Γ A' P).symm y))
  map_add' y y' := by simp
  map_smul' a y := by
    rw [orient_symm_smul, map_smul, orient_smul_left, RingHom.id_apply]

theorem fromOrient_apply (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) (y : A' ⊗[k] P) :
    fromOrient f y = orient k Γ A' Q (f ((orient k Γ A' P).symm y)) := rfl

theorem fromOrient_orient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q)
    (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    fromOrient f (orient k Γ A' P x) = orient k Γ A' Q (f x) := by
  rw [fromOrient_apply, LinearEquiv.symm_apply_apply]

theorem intertwines_fromOrient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    Intertwines (_root_.id : Γ → Γ) (fromOrient f) := fun s y => by
  rw [fromOrient_apply, fromOrient_apply, orient_symm_actR, map_smul, orient_smul_right]; rfl

noncomputable def toOrient (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (hf : Intertwines (_root_.id : Γ → Γ) f) :
    (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q where
  toFun x := (orient k Γ A' Q).symm (f (orient k Γ A' P x))
  map_add' x x' := by simp
  map_smul' b x := by
    rw [RingHom.id_apply]
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul γ a =>
      rw [orient_smul, map_smul, hf, LinearEquiv.symm_apply_eq, orient_smul, LinearEquiv.apply_symm_apply]
      rfl
    | add b b' hb hb' => simp only [add_smul, map_add, hb, hb']

theorem toOrient_apply (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (hf : Intertwines (_root_.id : Γ → Γ) f)
    (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    toOrient f hf x = (orient k Γ A' Q).symm (f (orient k Γ A' P x)) := rfl

theorem fromOrient_toOrient (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (hf : Intertwines (_root_.id : Γ → Γ) f) :
    fromOrient (toOrient f hf) = f := by
  refine LinearMap.ext fun y => ?_
  rw [fromOrient_apply, toOrient_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem toOrient_fromOrient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    toOrient (fromOrient f) (intertwines_fromOrient f) = f := by
  refine LinearMap.ext fun x => ?_
  rw [toOrient_apply, fromOrient_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

noncomputable def fromOrientEquiv (e : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q :=
  LinearEquiv.ofLinear (fromOrient (e : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q))
    (fromOrient (e.symm : (Γ ⊗[k] A') ⊗[Γ] Q →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] P))
    (by refine LinearMap.ext fun y => ?_; simp [fromOrient_apply])
    (by refine LinearMap.ext fun y => ?_; simp [fromOrient_apply])

@[scoped simp] theorem coe_fromOrientEquiv (e : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    (fromOrientEquiv e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) =
      fromOrient (e : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) := rfl

theorem fromOrientEquiv_apply (e : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) (y : A' ⊗[k] P) :
    fromOrientEquiv e y = orient k Γ A' Q (e ((orient k Γ A' P).symm y)) := rfl

noncomputable def toOrientEquiv (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q)
    (he : Intertwines (_root_.id : Γ → Γ) (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)) :
    (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q :=
  LinearEquiv.ofLinear (toOrient (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) he)
    (toOrient (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P)
      (by simpa using (Intertwines.symm (σ := Equiv.refl Γ) he)))
    (by refine LinearMap.ext fun y => ?_; simp [toOrient_apply])
    (by refine LinearMap.ext fun y => ?_; simp [toOrient_apply])

theorem toOrientEquiv_apply (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q)
    (he : Intertwines (_root_.id : Γ → Γ) (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)) (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    toOrientEquiv e he x = (orient k Γ A' Q).symm (e (orient k Γ A' P x)) := rfl

end Orient

section OneChart

variable {k : Type*} [CommRing k] {A' : Type*} [CommRing A'] [Algebra k A']
  {Γ : Type*} [CommRing Γ] [Algebra k Γ] {Γ' : Type*} [CommRing Γ'] [Algebra A' Γ']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {P' : Type*} [AddCommGroup P'] [Module Γ P'] [Module k P'] [IsScalarTower k Γ P']
  {Q : Type*} [AddCommGroup Q] [Module Γ' Q] [Module A' Q] [IsScalarTower A' Γ' Q]
  {Q' : Type*} [AddCommGroup Q'] [Module Γ' Q'] [Module A' Q'] [IsScalarTower A' Γ' Q']

omit [Algebra k A'] in
theorem smul_comm_of_tower (a : A') (t : Γ') (q : Q) : a • t • q = t • a • q := by
  rw [← algebraMap_smul Γ' a (t • q), smul_smul, mul_comm, ← smul_smul, algebraMap_smul]

theorem apply_actR_of_semilinear (φ : Γ → Γ') (β : A' ⊗[k] P ≃ₗ[A'] Q)
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (s : Γ) (x : A' ⊗[k] P) : β (actR k A' s x) = φ s • β x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [actR_tmul, tmul_eq_smul_one_tmul k A' a (s • m), map_smul, hs, tmul_eq_smul_one_tmul k A' a m,
      map_smul, smul_comm_of_tower]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

theorem symm_apply_smul_of_semilinear (φ : Γ → Γ') (β : A' ⊗[k] P ≃ₗ[A'] Q)
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (s : Γ) (q : Q) : β.symm (φ s • q) = actR k A' s (β.symm q) := by
  rw [LinearEquiv.symm_apply_eq, apply_actR_of_semilinear φ β hs, LinearEquiv.apply_symm_apply]

noncomputable def conjIn (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q') (ψ : Q ≃ₗ[Γ'] Q') :
    A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] P' :=
  β ≪≫ₗ ψ.restrictScalars A' ≪≫ₗ β'.symm

theorem conjIn_apply (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q') (ψ : Q ≃ₗ[Γ'] Q')
    (x : A' ⊗[k] P) : conjIn β β' ψ x = β'.symm (ψ (β x)) := rfl

theorem intertwines_conjIn (φ : Γ → Γ') (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q')
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (hs' : ∀ (s : Γ) (m : P'), β' ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β' ((1 : A') ⊗ₜ[k] m))
    (ψ : Q ≃ₗ[Γ'] Q') :
    Intertwines (_root_.id : Γ → Γ) (conjIn β β' ψ : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P') := fun s x => by
  simp only [LinearEquiv.coe_coe, conjIn_apply]
  rw [apply_actR_of_semilinear φ β hs, map_smul, symm_apply_smul_of_semilinear φ β' hs']; rfl

noncomputable def conjOut (φ : Γ → Γ') (hgen : ∀ y : Γ', y ∈ Submodule.span A' (Set.range φ))
    (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q')
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (hs' : ∀ (s : Γ) (m : P'), β' ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β' ((1 : A') ⊗ₜ[k] m))
    (f : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] P') (hf : Intertwines (_root_.id : Γ → Γ) (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P')) :
    Q ≃ₗ[Γ'] Q' :=
  let E : Q ≃ₗ[A'] Q' := β.symm ≪≫ₗ f ≪≫ₗ β'
  have hE : ∀ (y : Γ') (q : Q), E (y • q) = y • E q := fun y q => by

    suffices h : Submodule.span A' (Set.range φ) ≤
        { carrier := {y : Γ' | ∀ q : Q, E (y • q) = y • E q}
          add_mem' := fun {a b} ha hb q => by
            simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [add_smul, map_add, ha, hb, add_smul]
          zero_mem' := fun q => by simp
          smul_mem' := fun a y hy q => by
            simp only [Set.mem_setOf_eq] at hy ⊢
            rw [smul_assoc, map_smul, hy, smul_assoc] } from h (hgen y) q
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩ q
    simp only [E, LinearEquiv.trans_apply]
    rw [symm_apply_smul_of_semilinear φ β hs, ← LinearEquiv.coe_coe f, hf, LinearEquiv.coe_coe,
      apply_actR_of_semilinear φ β' hs']
    rfl
  { toFun := E
    invFun := E.symm
    map_add' := fun x y => E.map_add x y
    map_smul' := hE
    left_inv := E.left_inv
    right_inv := E.right_inv }

theorem conjOut_apply (φ : Γ → Γ') (hgen : ∀ y : Γ', y ∈ Submodule.span A' (Set.range φ))
    (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q')
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (hs' : ∀ (s : Γ) (m : P'), β' ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β' ((1 : A') ⊗ₜ[k] m))
    (f : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] P') (hf : Intertwines (_root_.id : Γ → Γ) (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P'))
    (q : Q) : conjOut φ hgen β β' hs hs' f hf q = β' (f (β.symm q)) := rfl

end OneChart

section TwoChart

open TwoChartCech

variable {k : Type u} [CommRing k] {A' : Type u} [CommRing A'] [Algebra k A']
  {𝒰 : Cover.{u, u} k} {𝒰' : Cover.{u, u} A'}

structure ChartBC (φ0 : 𝒰.A0 → 𝒰'.A0) (φ1 : 𝒰.A1 → 𝒰'.A1) (φ01 : 𝒰.A01 → 𝒰'.A01)
    (S : Sections.{u, u, w} 𝒰) (T : Sections.{u, u, w} 𝒰') where
  β0 : A' ⊗[k] S.M0 ≃ₗ[A'] T.M0
  β1 : A' ⊗[k] S.M1 ≃ₗ[A'] T.M1
  β01 : A' ⊗[k] S.M01 ≃ₗ[A'] T.M01
  hr0 : ∀ x, β01 (S.r0.baseChange A' x) = T.r0 (β0 x)
  hr1 : ∀ x, β01 (S.r1.baseChange A' x) = T.r1 (β1 x)
  hs0 : ∀ (s : 𝒰.A0) (m : S.M0), β0 ((1 : A') ⊗ₜ[k] (s • m)) = φ0 s • β0 ((1 : A') ⊗ₜ[k] m)
  hs1 : ∀ (s : 𝒰.A1) (m : S.M1), β1 ((1 : A') ⊗ₜ[k] (s • m)) = φ1 s • β1 ((1 : A') ⊗ₜ[k] m)
  hs01 : ∀ (s : 𝒰.A01) (m : S.M01), β01 ((1 : A') ⊗ₜ[k] (s • m)) = φ01 s • β01 ((1 : A') ⊗ₜ[k] m)

variable {φ0 : 𝒰.A0 → 𝒰'.A0} {φ1 : 𝒰.A1 → 𝒰'.A1} {φ01 : 𝒰.A01 → 𝒰'.A01}
  {S S' : Sections.{u, u, w} 𝒰} {T T' : Sections.{u, u, w} 𝒰'}

theorem ChartBC.exists_intertwines_of_chartIso (β : ChartBC φ0 φ1 φ01 S T) (β' : ChartBC φ0 φ1 φ01 S' T')
    (ψ0 : T.M0 ≃ₗ[𝒰'.A0] T'.M0) (ψ1 : T.M1 ≃ₗ[𝒰'.A1] T'.M1) (ψ01 : T.M01 ≃ₗ[𝒰'.A01] T'.M01)
    (hψ0 : ∀ m, ψ01 (T.r0 m) = T'.r0 (ψ0 m)) (hψ1 : ∀ m, ψ01 (T.r1 m) = T'.r1 (ψ1 m)) :
    ∃ (e0 : A' ⊗[k] S.M0 ≃ₗ[A'] A' ⊗[k] S'.M0) (e1 : A' ⊗[k] S.M1 ≃ₗ[A'] A' ⊗[k] S'.M1)
      (e01 : A' ⊗[k] S.M01 ≃ₗ[A'] A' ⊗[k] S'.M01),
      Intertwines (_root_.id : 𝒰.A0 → 𝒰.A0) (e0 : A' ⊗[k] S.M0 →ₗ[A'] A' ⊗[k] S'.M0) ∧
      Intertwines (_root_.id : 𝒰.A1 → 𝒰.A1) (e1 : A' ⊗[k] S.M1 →ₗ[A'] A' ⊗[k] S'.M1) ∧
      Intertwines (_root_.id : 𝒰.A01 → 𝒰.A01) (e01 : A' ⊗[k] S.M01 →ₗ[A'] A' ⊗[k] S'.M01) ∧
      (∀ x, e01 (S.r0.baseChange A' x) = S'.r0.baseChange A' (e0 x)) ∧
      (∀ x, e01 (S.r1.baseChange A' x) = S'.r1.baseChange A' (e1 x)) := by
  refine ⟨conjIn β.β0 β'.β0 ψ0, conjIn β.β1 β'.β1 ψ1, conjIn β.β01 β'.β01 ψ01,
    intertwines_conjIn φ0 _ _ β.hs0 β'.hs0 ψ0, intertwines_conjIn φ1 _ _ β.hs1 β'.hs1 ψ1,
    intertwines_conjIn φ01 _ _ β.hs01 β'.hs01 ψ01, fun x => ?_, fun x => ?_⟩
  · rw [conjIn_apply, conjIn_apply, LinearEquiv.symm_apply_eq]
    change ψ01 (β.β01 _) = β'.β01 (S'.r0.baseChange A' (β'.β0.symm (ψ0 (β.β0 x))))
    rw [β.hr0, β'.hr0, LinearEquiv.apply_symm_apply, hψ0]
  · rw [conjIn_apply, conjIn_apply, LinearEquiv.symm_apply_eq]
    change ψ01 (β.β01 _) = β'.β01 (S'.r1.baseChange A' (β'.β1.symm (ψ1 (β.β1 x))))
    rw [β.hr1, β'.hr1, LinearEquiv.apply_symm_apply, hψ1]

theorem ChartBC.exists_chartIso_of_intertwines (β : ChartBC φ0 φ1 φ01 S T) (β' : ChartBC φ0 φ1 φ01 S' T')
    (hgen0 : ∀ y : 𝒰'.A0, y ∈ Submodule.span A' (Set.range φ0))
    (hgen1 : ∀ y : 𝒰'.A1, y ∈ Submodule.span A' (Set.range φ1))
    (hgen01 : ∀ y : 𝒰'.A01, y ∈ Submodule.span A' (Set.range φ01))
    (f0 : A' ⊗[k] S.M0 ≃ₗ[A'] A' ⊗[k] S'.M0) (f1 : A' ⊗[k] S.M1 ≃ₗ[A'] A' ⊗[k] S'.M1)
    (f01 : A' ⊗[k] S.M01 ≃ₗ[A'] A' ⊗[k] S'.M01)
    (hf0 : Intertwines (_root_.id : 𝒰.A0 → 𝒰.A0) (f0 : A' ⊗[k] S.M0 →ₗ[A'] A' ⊗[k] S'.M0))
    (hf1 : Intertwines (_root_.id : 𝒰.A1 → 𝒰.A1) (f1 : A' ⊗[k] S.M1 →ₗ[A'] A' ⊗[k] S'.M1))
    (hf01 : Intertwines (_root_.id : 𝒰.A01 → 𝒰.A01) (f01 : A' ⊗[k] S.M01 →ₗ[A'] A' ⊗[k] S'.M01))
    (hsq0 : ∀ x, f01 (S.r0.baseChange A' x) = S'.r0.baseChange A' (f0 x))
    (hsq1 : ∀ x, f01 (S.r1.baseChange A' x) = S'.r1.baseChange A' (f1 x)) :
    ∃ (E0 : T.M0 ≃ₗ[𝒰'.A0] T'.M0) (E1 : T.M1 ≃ₗ[𝒰'.A1] T'.M1) (E01 : T.M01 ≃ₗ[𝒰'.A01] T'.M01),
      (∀ m, E01 (T.r0 m) = T'.r0 (E0 m)) ∧ (∀ m, E01 (T.r1 m) = T'.r1 (E1 m)) := by
  refine ⟨conjOut φ0 hgen0 β.β0 β'.β0 β.hs0 β'.hs0 f0 hf0, conjOut φ1 hgen1 β.β1 β'.β1 β.hs1 β'.hs1 f1 hf1,
    conjOut φ01 hgen01 β.β01 β'.β01 β.hs01 β'.hs01 f01 hf01, fun m => ?_, fun m => ?_⟩
  · rw [conjOut_apply, conjOut_apply]
    obtain ⟨x, rfl⟩ := β.β0.surjective m
    rw [← β.hr0, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hsq0, β'.hr0]
  · rw [conjOut_apply, conjOut_apply]
    obtain ⟨x, rfl⟩ := β.β1.surjective m
    rw [← β.hr1, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hsq1, β'.hr1]

end TwoChart

section Present

variable (k : Type*) [CommRing k] (A' : Type*) [CommRing A'] [Algebra k A']
  (S : Type*) [CommRing S] [Algebra k S] (S' : Type*) [CommRing S'] [Algebra k S'] [Algebra A' S']
  [IsScalarTower k A' S']
  (B : Type*) [CommRing B] [Algebra B S] [Algebra B S']
  (L : Type*) [AddCommGroup L] [Module B L]
  [SMulCommClass B k S] [SMulCommClass B A' S']

set_option maxHeartbeats 6400000 in

theorem exists_presentEquiv (φ : S →+* S') (e : A' ⊗[k] S ≃ₐ[A'] S') (he : ∀ s, e ((1 : A') ⊗ₜ[k] s) = φ s)
    (hB : ∀ b, algebraMap B S' b = φ (algebraMap B S b)) :
    ∃ Z : A' ⊗[k] (S ⊗[B] L) ≃ₗ[A'] S' ⊗[B] L,
      (∀ (a : A') (s : S) (l : L), Z (a ⊗ₜ[k] (s ⊗ₜ[B] l)) = (a • φ s) ⊗ₜ[B] l) ∧
      (∀ (a : A') (s : S) (p : S ⊗[B] L), Z (a ⊗ₜ[k] (s • p)) = (a • φ s) • Z ((1 : A') ⊗ₜ[k] p)) := by
  letI : Algebra S S' := φ.toAlgebra
  haveI : IsScalarTower B S S' := IsScalarTower.of_algebraMap_eq fun b => by
    rw [RingHom.algebraMap_toAlgebra]; exact hB b

  let ce : S ⊗[k] A' ≃ₐ[k] S' := (Algebra.TensorProduct.comm k S A').trans (e.restrictScalars k)
  have hce : ∀ (s : S) (a : A'), ce (s ⊗ₜ[k] a) = φ s * algebraMap A' S' a := fun s a => by
    change e (a ⊗ₜ[k] s) = _
    rw [show a ⊗ₜ[k] s = (a ⊗ₜ[k] (1 : S)) * ((1 : A') ⊗ₜ[k] s) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, he,
      show a ⊗ₜ[k] (1 : S) = algebraMap A' (A' ⊗[k] S) a from rfl, AlgEquiv.commutes, mul_comm]
  let e' : S ⊗[k] A' ≃ₗ[S] S' :=
    { toFun := ce, invFun := ce.symm, map_add' := fun x y => map_add ce x y
      map_smul' := fun s x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, map_mul, hce, map_one, mul_one, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      left_inv := ce.left_inv, right_inv := ce.right_inv }
  have he' : ∀ a : A', e' ((1 : S) ⊗ₜ[k] a) = algebraMap A' S' a := fun a => by
    change ce _ = _; rw [hce, map_one, one_mul]
  let Zf : A' ⊗[k] (S ⊗[B] L) → S' ⊗[B] L := fun x =>
    TensorProduct.AlgebraTensorModule.cancelBaseChange B S S' S' L
      (LinearEquiv.rTensor (S ⊗[B] L) e' ((orient k S A' (S ⊗[B] L)).symm x))
  let Zg : S' ⊗[B] L → A' ⊗[k] (S ⊗[B] L) := fun y =>
    orient k S A' (S ⊗[B] L) ((LinearEquiv.rTensor (S ⊗[B] L) e').symm
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange B S S' S' L).symm y))
  have hadd : ∀ x y, Zf (x + y) = Zf x + Zf y := fun x y => by simp only [Zf, map_add]
  have hZ : ∀ (a : A') (s : S) (l : L), Zf (a ⊗ₜ[k] (s ⊗ₜ[B] l)) = (a • φ s) ⊗ₜ[B] l := fun a s l => by
    simp only [Zf]
    rw [orient_symm_tmul, LinearEquiv.rTensor_tmul, he', TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      Algebra.smul_def, RingHom.algebraMap_toAlgebra, Algebra.smul_def, mul_comm]
  have hZs : ∀ (a : A') (s : S) (p : S ⊗[B] L), Zf (a ⊗ₜ[k] (s • p)) = (a • φ s) • Zf ((1 : A') ⊗ₜ[k] p) := by
    intro a s p
    induction p using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, smul_zero, Zf, map_zero]
    | tmul u l =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hZ, hZ, one_smul, TensorProduct.smul_tmul', smul_eq_mul, map_mul,
        smul_mul_assoc]
    | add x y hx hy => simp only [smul_add, tmul_add, hadd, hx, hy]
  have hlin : ∀ (a : A') (x : A' ⊗[k] (S ⊗[B] L)), Zf (a • x) = a • Zf x := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, Zf, map_zero]
    | tmul a' p =>
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      induction p using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, Zf, map_zero, smul_zero]
      | tmul s l => rw [hZ, hZ, TensorProduct.smul_tmul', mul_smul]
      | add x y hx hy => simp only [tmul_add, hadd, smul_add, hx, hy]
    | add x y hx hy => simp only [smul_add, hadd, hx, hy]
  have hgf : ∀ x, Zg (Zf x) = x := fun x => by simp only [Zf, Zg, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  have hfg : ∀ y, Zf (Zg y) = y := fun y => by simp only [Zf, Zg, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  let Z : A' ⊗[k] (S ⊗[B] L) ≃ₗ[A'] S' ⊗[B] L :=
    { toFun := Zf
      invFun := Zg
      map_add' := hadd
      map_smul' := hlin
      left_inv := hgf
      right_inv := hfg }
  exact ⟨Z, hZ, hZs⟩

end Present

end AlgebraicGeometry.RelPicard.LFP
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Spec Scheme Scheme.Hom.naturality Scheme.Modules Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap FGSubalgebra RelPicard.LFP.stageHom"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle LFP.stageHom RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom"
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

section Vertex

variable {ι : Type v} {B₀ : Type u} [CommRing B₀] {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    {Bω : Type u} [CommRing Bω] [Algebra B₀ Bω] {Bω' : Type u} [CommRing Bω'] [Algebra B₀ Bω']

theorem vertex_comp [Preorder ι] (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i) (h : Bω ≃ₐ[B₀] Bω') (i j : ι) (hij : i ≤ j) :
    ((h : Bω →ₐ[B₀] Bω').comp (g j)).comp (τ i j hij) = (h : Bω →ₐ[B₀] Bω').comp (g i) := by
  rw [AlgHom.comp_assoc, hg]

theorem vertex_surj (g : ∀ i, B i →ₐ[B₀] Bω) (hsurj : ∀ b : Bω, ∃ i x, g i x = b) (h : Bω ≃ₐ[B₀] Bω')
    (b : Bω') : ∃ i x, ((h : Bω →ₐ[B₀] Bω').comp (g i)) x = b := by
  obtain ⟨i, x, hx⟩ := hsurj (h.symm b)
  exact ⟨i, x, by simp [hx]⟩

theorem vertex_zero [Preorder ι] (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) (g : ∀ i, B i →ₐ[B₀] Bω)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0) (h : Bω ≃ₐ[B₀] Bω')
    (i : ι) (x : B i) (hx : ((h : Bω →ₐ[B₀] Bω').comp (g i)) x = 0) : ∃ (j : ι) (hij : i ≤ j), τ i j hij x = 0 :=
  hzero i x (by simpa using hx)

end Vertex
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"

theorem smulCommClass_of_algebras (R₁ R₂ T : Type*) [CommSemiring R₁] [CommSemiring R₂] [CommSemiring T]
    [Algebra R₁ T] [Algebra R₂ T] : SMulCommClass R₁ R₂ T :=
  ⟨fun a b t => by simp only [Algebra.smul_def]; ring⟩

theorem one_tmul_tmul_tmul {B0 B' B'' V : Type*} [CommRing B0] [CommRing B'] [CommRing B''] [CommRing V]
    [Algebra B0 B'] [Algebra B' B''] [Algebra B'' V] {L : Type*} [AddCommGroup L] [Module B0 L]
    (b : B'') (β : B') (l : L) :
    ((1 : V) ⊗ₜ[B''] (b ⊗ₜ[B'] (β ⊗ₜ[B0] l)) : V ⊗[B''] (B'' ⊗[B'] (B' ⊗[B0] L))) =
      (algebraMap B'' V (β • b)) ⊗ₜ[B''] ((1 : B'') ⊗ₜ[B'] ((1 : B') ⊗ₜ[B0] l)) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem finrank_baseChange_eq_one_of_invertible {A : Type*} [CommRing A] (P : Type*) [AddCommGroup P] [Module A P]
    [Module.Invertible A P] (K : Type*) [Field K] [Algebra A K] : Module.finrank K (K ⊗[A] P) = 1 :=
  Module.Invertible.finrank_eq_one K (K ⊗[A] P)

end AlgebraicGeometry.RelPicard.LFP
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Spec Scheme Scheme.Hom.naturality Scheme.Modules Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap FGSubalgebra RelPicard.LFP.stageHom"
p2m_open "AlgebraicGeometry"

open CategoryTheory Opposite

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Modules.pullback Hom mk Hom.appLE_comp_appLE Γ Hom.naturality Modules Opens Hom.appLE_map Hom.app_eq_appLE Cover TwoAffineOpenCover TwoAffineOpenCover.specMap" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "map_appLE image appLE_comp_appLE app injective surjective mk naturality cover appLE_map app_eq_appLE comp_apply appLE finrank" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.appLE_app_apply_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k) (U : Z.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U))
    (s : Γ(Z, U)) : (f.appLE (g ⁻¹ᵁ U) V e).hom ((g.app U).hom s) = (k.appLE U V (by subst h; exact e)).hom s := by
  subst h
  rw [← CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.appLE_apply_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U') (hU : U' ≤ U) (hV : V' ≤ V) (s : Γ(Y, U)) :
    (f.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom s) =
      (X.presheaf.map (homOfLE hV).op).hom ((f.appLE U V e).hom s) := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.app_apply_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U) (s : Γ(Y, U)) :
    (f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom s) =
      (X.presheaf.map (homOfLE (show f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U from fun _ hx => hU hx)).op).hom ((f.app U).hom s) := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Spec Scheme Scheme.Hom.naturality Scheme.Modules Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap FGSubalgebra RelPicard.LFP.stageHom"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle LFP.stageHom RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom"
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

section VertexGeo

p2m_open "AlgebraicGeometry.FGSubalgebra"

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (Γ : Type u) [CommRing Γ] [Algebra R Γ]

@[reducible] noncomputable def algebraOfPresent (U : Type u) [CommRing U] [Algebra A U] (eU : A ⊗[R] Γ ≃ₐ[A] U) :
    Algebra Γ U :=
  ((eU : A ⊗[R] Γ ≃+* U).toRingHom.comp (Algebra.TensorProduct.includeRight : Γ →ₐ[R] A ⊗[R] Γ).toRingHom).toAlgebra

noncomputable def vtxEquiv (U : Type u) [CommRing U] [Algebra A U] (eU : A ⊗[R] Γ ≃ₐ[A] U) :
    letI := algebraOfPresent R A Γ U eU; Γ ⊗[R] A ≃ₐ[Γ] U :=
  letI := algebraOfPresent R A Γ U eU
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R Γ A).toRingEquiv.trans (eU : A ⊗[R] Γ ≃+* U)) (fun _ => rfl)

noncomputable def vtxHom (U : Type u) [CommRing U] [Algebra A U] (eU : A ⊗[R] Γ ≃ₐ[A] U) (D : FGSubalgebra R A) :
    letI := algebraOfPresent R A Γ U eU; tensorStage R A Γ D →ₐ[Γ] U :=
  letI := algebraOfPresent R A Γ U eU
  (vtxEquiv R A Γ U eU : Γ ⊗[R] A →ₐ[Γ] U).comp (tensorStageToColimit R A Γ D)

variable (U : Type u) [CommRing U] [Algebra A U] (eU : A ⊗[R] Γ ≃ₐ[A] U)

theorem vtxHom_tmul (D : FGSubalgebra R A) (γ : Γ) (d : ↥D.1) :
    vtxHom R A Γ U eU D (γ ⊗ₜ[R] d) = eU ((d : A) ⊗ₜ[R] γ) := rfl

theorem vtxHom_comp (i j : FGSubalgebra R A) (h : i ≤ j) :
    letI := algebraOfPresent R A Γ U eU
    (vtxHom R A Γ U eU j).comp (tensorStageMap R A Γ i j h) = vtxHom R A Γ U eU i :=
  letI := algebraOfPresent R A Γ U eU
  vertex_comp (fun i j h => tensorStageMap R A Γ i j h) (tensorStageToColimit R A Γ) (tensorStageToColimit_comp R A Γ)
    (vtxEquiv R A Γ U eU) i j h

theorem vtxHom_surj (b : U) : ∃ (i : FGSubalgebra R A) (x : tensorStage R A Γ i), vtxHom R A Γ U eU i x = b :=
  letI := algebraOfPresent R A Γ U eU
  vertex_surj (tensorStageToColimit R A Γ) (tensorStageToColimit_surj R A Γ) (vtxEquiv R A Γ U eU) b

theorem vtxHom_zero (i : FGSubalgebra R A) (x : tensorStage R A Γ i) (hx : vtxHom R A Γ U eU i x = 0) :
    ∃ (j : FGSubalgebra R A) (h : i ≤ j), tensorStageMap R A Γ i j h x = 0 :=
  letI := algebraOfPresent R A Γ U eU
  vertex_zero (fun i j h => tensorStageMap R A Γ i j h) (tensorStageToColimit R A Γ) (tensorStageToColimit_zero R A Γ)
    (vtxEquiv R A Γ U eU) i x hx

noncomputable def stgHom (D : FGSubalgebra R A) (W : Type u) [CommRing W] [Algebra (↥D.1) W]
    (eW : ↥D.1 ⊗[R] Γ ≃ₐ[↥D.1] W) : tensorStage R A Γ D →+* W :=
  (eW : ↥D.1 ⊗[R] Γ ≃+* W).toRingHom.comp (Algebra.TensorProduct.comm R Γ ↥D.1 : Γ ⊗[R] ↥D.1 ≃ₐ[R] ↥D.1 ⊗[R] Γ).toRingHom

theorem stgHom_tmul (D : FGSubalgebra R A) (W : Type u) [CommRing W] [Algebra (↥D.1) W]
    (eW : ↥D.1 ⊗[R] Γ ≃ₐ[↥D.1] W) (γ : Γ) (d : ↥D.1) : stgHom R A Γ D W eW (γ ⊗ₜ[R] d) = eW (d ⊗ₜ[R] γ) := rfl

end VertexGeo
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"

section AbstractSurj

p2m_open "TwoChartCech AlgebraicGeometry.FGSubalgebra"

set_option maxHeartbeats 48000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem exists_fg_gluingData
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    (𝒰 : Cover.{u, u} R) (UA : Cover.{u, u} A) (T : Sections.{u, u, w} UA)
    [Module.Invertible UA.A0 T.M0] [Module.Invertible UA.A1 T.M1]
    (eU0 : A ⊗[R] 𝒰.A0 ≃ₐ[A] UA.A0) (eU1 : A ⊗[R] 𝒰.A1 ≃ₐ[A] UA.A1) (eU01 : A ⊗[R] 𝒰.A01 ≃ₐ[A] UA.A01)
    (hρU0 : ∀ (a : A) (γ : 𝒰.A0), UA.ρ0 (eU0 (a ⊗ₜ[R] γ)) = eU01 (a ⊗ₜ[R] 𝒰.ρ0 γ))
    (hρU1 : ∀ (a : A) (γ : 𝒰.A1), UA.ρ1 (eU1 (a ⊗ₜ[R] γ)) = eU01 (a ⊗ₜ[R] 𝒰.ρ1 γ))
    (rbc0 : letI := UA.ρ0.toRingHom.toAlgebra; UA.A01 ⊗[UA.A0] T.M0 ≃ₗ[UA.A01] T.M01)
    (hrbc0 : letI := UA.ρ0.toRingHom.toAlgebra; ∀ m, rbc0 ((1 : UA.A01) ⊗ₜ[UA.A0] m) = T.r0 m)
    (rbc1 : letI := UA.ρ1.toRingHom.toAlgebra; UA.A01 ⊗[UA.A1] T.M1 ≃ₗ[UA.A01] T.M01)
    (hrbc1 : letI := UA.ρ1.toRingHom.toAlgebra; ∀ m, rbc1 ((1 : UA.A01) ⊗ₜ[UA.A1] m) = T.r1 m)
    (V : ∀ D : FGSubalgebra R A, Cover.{u, u} ↥D.1)
    (eV0 : ∀ D : FGSubalgebra R A, ↥D.1 ⊗[R] 𝒰.A0 ≃ₐ[↥D.1] (V D).A0)
    (eV1 : ∀ D : FGSubalgebra R A, ↥D.1 ⊗[R] 𝒰.A1 ≃ₐ[↥D.1] (V D).A1)
    (eV01 : ∀ D : FGSubalgebra R A, ↥D.1 ⊗[R] 𝒰.A01 ≃ₐ[↥D.1] (V D).A01)
    (hρV0 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A0), (V D).ρ0 (eV0 D (d ⊗ₜ[R] γ)) = eV01 D (d ⊗ₜ[R] 𝒰.ρ0 γ))
    (hρV1 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A1), (V D).ρ1 (eV1 D (d ⊗ₜ[R] γ)) = eV01 D (d ⊗ₜ[R] 𝒰.ρ1 γ))
    (φ0 : ∀ D : FGSubalgebra R A, (V D).A0 →+* UA.A0) (φ1 : ∀ D : FGSubalgebra R A, (V D).A1 →+* UA.A1)
    (φ01 : ∀ D : FGSubalgebra R A, (V D).A01 →+* UA.A01)
    (eφ0 : ∀ D : FGSubalgebra R A, A ⊗[↥D.1] (V D).A0 ≃ₐ[A] UA.A0)
    (heφ0 : ∀ (D : FGSubalgebra R A) (s : (V D).A0), eφ0 D ((1 : A) ⊗ₜ[↥D.1] s) = φ0 D s)
    (eφ1 : ∀ D : FGSubalgebra R A, A ⊗[↥D.1] (V D).A1 ≃ₐ[A] UA.A1)
    (heφ1 : ∀ (D : FGSubalgebra R A) (s : (V D).A1), eφ1 D ((1 : A) ⊗ₜ[↥D.1] s) = φ1 D s)
    (eφ01 : ∀ D : FGSubalgebra R A, A ⊗[↥D.1] (V D).A01 ≃ₐ[A] UA.A01)
    (heφ01 : ∀ (D : FGSubalgebra R A) (s : (V D).A01), eφ01 D ((1 : A) ⊗ₜ[↥D.1] s) = φ01 D s)
    (hφρ0 : ∀ (D : FGSubalgebra R A) (s : (V D).A0), φ01 D ((V D).ρ0 s) = UA.ρ0 (φ0 D s))
    (hφρ1 : ∀ (D : FGSubalgebra R A) (s : (V D).A1), φ01 D ((V D).ρ1 s) = UA.ρ1 (φ1 D s))
    (hφe0 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A0), φ0 D (eV0 D (d ⊗ₜ[R] γ)) = eU0 ((d : A) ⊗ₜ[R] γ))
    (hφe1 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A1), φ1 D (eV1 D (d ⊗ₜ[R] γ)) = eU1 ((d : A) ⊗ₜ[R] γ))
    (hφe01 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A01), φ01 D (eV01 D (d ⊗ₜ[R] γ)) = eU01 ((d : A) ⊗ₜ[R] γ)) :
    ∃ (D : FGSubalgebra R A)
      (P0 : Type u) (_ : AddCommGroup P0) (_ : Module (V D).A0 P0) (_ : Module.Finite (V D).A0 P0)
      (_ : Module.Projective (V D).A0 P0)
      (P1 : Type u) (_ : AddCommGroup P1) (_ : Module (V D).A1 P1) (_ : Module.Finite (V D).A1 P1)
      (_ : Module.Projective (V D).A1 P1)
      (_ : ∀ (K : Type u) [Field K] [Algebra (V D).A0 K], Module.finrank K (K ⊗[(V D).A0] P0) = 1)
      (_ : ∀ (K : Type u) [Field K] [Algebra (V D).A1 K], Module.finrank K (K ⊗[(V D).A1] P1) = 1)
      (σ : letI := (V D).ρ0.toRingHom.toAlgebra; letI := (V D).ρ1.toRingHom.toAlgebra
        (V D).A01 ⊗[(V D).A0] P0 ≃ₗ[(V D).A01] (V D).A01 ⊗[(V D).A1] P1),
      ∀ (S : Sections.{u, u, w} (V D)) (e0 : S.M0 ≃ₗ[(V D).A0] P0) (e1 : S.M1 ≃ₗ[(V D).A1] P1)
        (e01 : letI := (V D).ρ0.toRingHom.toAlgebra; S.M01 ≃ₗ[(V D).A01] (V D).A01 ⊗[(V D).A0] P0),
        (letI := (V D).ρ0.toRingHom.toAlgebra; ∀ m, e01 (S.r0 m) = (1 : (V D).A01) ⊗ₜ[(V D).A0] e0 m) →
        (letI := (V D).ρ0.toRingHom.toAlgebra; letI := (V D).ρ1.toRingHom.toAlgebra
          ∀ m, σ (e01 (S.r1 m)) = (1 : (V D).A01) ⊗ₜ[(V D).A1] e1 m) →
        Nonempty (ChartBC (k := ↥D.1) (A' := A) (φ0 D) (φ1 D) (φ01 D) S T) := by
  classical
  haveI : IsDirectedOrder (FGSubalgebra R A) := ⟨IsDirected.directed⟩

  letI algΓU0 : Algebra 𝒰.A0 UA.A0 := algebraOfPresent R A 𝒰.A0 UA.A0 eU0
  letI algΓU1 : Algebra 𝒰.A1 UA.A1 := algebraOfPresent R A 𝒰.A1 UA.A1 eU1
  letI algΓU01 : Algebra 𝒰.A01 UA.A01 := algebraOfPresent R A 𝒰.A01 UA.A01 eU01

  obtain ⟨D0, L0, _, _, hinv0, ⟨ι0⟩⟩ := Module.IsDirectLimit.exists_invertible_linearEquiv_baseChange
    (tensorStage R A 𝒰.A0) (fun i j h => tensorStageMap R A 𝒰.A0 i j h) UA.A0 (vtxHom R A 𝒰.A0 UA.A0 eU0)
    (vtxHom_comp R A 𝒰.A0 UA.A0 eU0) (vtxHom_surj R A 𝒰.A0 UA.A0 eU0) (vtxHom_zero R A 𝒰.A0 UA.A0 eU0) T.M0
  obtain ⟨D1, L1, _, _, hinv1, ⟨ι1⟩⟩ := Module.IsDirectLimit.exists_invertible_linearEquiv_baseChange
    (tensorStage R A 𝒰.A1) (fun i j h => tensorStageMap R A 𝒰.A1 i j h) UA.A1 (vtxHom R A 𝒰.A1 UA.A1 eU1)
    (vtxHom_comp R A 𝒰.A1 UA.A1 eU1) (vtxHom_surj R A 𝒰.A1 UA.A1 eU1) (vtxHom_zero R A 𝒰.A1 UA.A1 eU1) T.M1
  haveI := hinv0
  haveI := hinv1
  letI algB0U0 : Algebra (tensorStage R A 𝒰.A0 D0) UA.A0 := (vtxHom R A 𝒰.A0 UA.A0 eU0 D0).toRingHom.toAlgebra
  letI algB1U1 : Algebra (tensorStage R A 𝒰.A1 D1) UA.A1 := (vtxHom R A 𝒰.A1 UA.A1 eU1 D1).toRingHom.toAlgebra

  obtain ⟨D2, h02, h12⟩ := directed_of (· ≤ ·) D0 D1
  letI algB0B' : Algebra (tensorStage R A 𝒰.A0 D0) (tensorStage R A 𝒰.A01 D2) :=
    (Algebra.TensorProduct.map 𝒰.ρ0 (Subalgebra.inclusion (show D0.1 ≤ D2.1 from h02))).toRingHom.toAlgebra
  letI algB1B' : Algebra (tensorStage R A 𝒰.A1 D1) (tensorStage R A 𝒰.A01 D2) :=
    (Algebra.TensorProduct.map 𝒰.ρ1 (Subalgebra.inclusion (show D1.1 ≤ D2.1 from h12))).toRingHom.toAlgebra
  letI algB'U01 : Algebra (tensorStage R A 𝒰.A01 D2) UA.A01 := (vtxHom R A 𝒰.A01 UA.A01 eU01 D2).toRingHom.toAlgebra
  letI algU0U01 : Algebra UA.A0 UA.A01 := UA.ρ0.toRingHom.toAlgebra
  letI algU1U01 : Algebra UA.A1 UA.A01 := UA.ρ1.toRingHom.toAlgebra
  letI algB0U01 : Algebra (tensorStage R A 𝒰.A0 D0) UA.A01 :=
    (UA.ρ0.toRingHom.comp (vtxHom R A 𝒰.A0 UA.A0 eU0 D0).toRingHom).toAlgebra
  letI algB1U01 : Algebra (tensorStage R A 𝒰.A1 D1) UA.A01 :=
    (UA.ρ1.toRingHom.comp (vtxHom R A 𝒰.A1 UA.A1 eU1 D1).toRingHom).toAlgebra
  haveI towB0U0U01 : IsScalarTower (tensorStage R A 𝒰.A0 D0) UA.A0 UA.A01 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI towB1U1U01 : IsScalarTower (tensorStage R A 𝒰.A1 D1) UA.A1 UA.A01 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI towB0B'U01 : IsScalarTower (tensorStage R A 𝒰.A0 D0) (tensorStage R A 𝒰.A01 D2) UA.A01 := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul γ d =>
      change UA.ρ0 (vtxHom R A 𝒰.A0 UA.A0 eU0 D0 (γ ⊗ₜ[R] d)) =
        vtxHom R A 𝒰.A01 UA.A01 eU01 D2 (Algebra.TensorProduct.map 𝒰.ρ0 (Subalgebra.inclusion (show D0.1 ≤ D2.1 from h02)) (γ ⊗ₜ[R] d))
      rw [Algebra.TensorProduct.map_tmul, vtxHom_tmul, vtxHom_tmul]
      exact hρU0 d γ
    | add x y hx hy => simp only [map_add, hx, hy]
  haveI towB1B'U01 : IsScalarTower (tensorStage R A 𝒰.A1 D1) (tensorStage R A 𝒰.A01 D2) UA.A01 := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul γ d =>
      change UA.ρ1 (vtxHom R A 𝒰.A1 UA.A1 eU1 D1 (γ ⊗ₜ[R] d)) =
        vtxHom R A 𝒰.A01 UA.A01 eU01 D2 (Algebra.TensorProduct.map 𝒰.ρ1 (Subalgebra.inclusion (show D1.1 ≤ D2.1 from h12)) (γ ⊗ₜ[R] d))
      rw [Algebra.TensorProduct.map_tmul, vtxHom_tmul, vtxHom_tmul]
      exact hρU1 d γ
    | add x y hx hy => simp only [map_add, hx, hy]
  haveI : Module.FinitePresentation (tensorStage R A 𝒰.A01 D2) (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A0 D0] L0) :=
    Module.finitePresentation_of_projective (tensorStage R A 𝒰.A01 D2)
      (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A0 D0] L0)
  haveI : Module.FinitePresentation (tensorStage R A 𝒰.A01 D2) (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A1 D1] L1) :=
    Module.finitePresentation_of_projective (tensorStage R A 𝒰.A01 D2)
      (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A1 D1] L1)

  let θ0' : UA.A01 ⊗[tensorStage R A 𝒰.A0 D0] L0 ≃ₗ[UA.A01] T.M01 :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) UA.A0 UA.A01 UA.A01 L0).symm ≪≫ₗ
      (LinearEquiv.baseChange UA.A0 UA.A01 _ _ ι0) ≪≫ₗ rbc0
  let θ1' : UA.A01 ⊗[tensorStage R A 𝒰.A1 D1] L1 ≃ₗ[UA.A01] T.M01 :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A1 D1) UA.A1 UA.A01 UA.A01 L1).symm ≪≫ₗ
      (LinearEquiv.baseChange UA.A1 UA.A01 _ _ ι1) ≪≫ₗ rbc1
  let θ0 : UA.A01 ⊗[tensorStage R A 𝒰.A01 D2] (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A0 D0] L0) ≃ₗ[UA.A01] T.M01 :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (tensorStage R A 𝒰.A01 D2)
      UA.A01 UA.A01 L0) ≪≫ₗ θ0'
  let θ1 : UA.A01 ⊗[tensorStage R A 𝒰.A01 D2] (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A1 D1] L1) ≃ₗ[UA.A01] T.M01 :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A1 D1) (tensorStage R A 𝒰.A01 D2)
      UA.A01 UA.A01 L1) ≪≫ₗ θ1'

  obtain ⟨D3, h23, g'', hg'', σ3, hσ3⟩ := Module.IsDirectLimit.exists_stage_linearEquiv_of_finitePresentation_compat
    (tensorStage R A 𝒰.A01)
    (fun i j h => tensorStageMap R A 𝒰.A01 i j h) UA.A01 (vtxHom R A 𝒰.A01 UA.A01 eU01)
    (vtxHom_comp R A 𝒰.A01 UA.A01 eU01) (vtxHom_surj R A 𝒰.A01 UA.A01 eU01) (vtxHom_zero R A 𝒰.A01 UA.A01 eU01)
    D2 (fun _ => rfl) (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A0 D0] L0)
      (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A1 D1] L1) (θ0 ≪≫ₗ θ1.symm)
  letI algB'B'' : Algebra (tensorStage R A 𝒰.A01 D2) (tensorStage R A 𝒰.A01 D3) :=
    (tensorStageMap R A 𝒰.A01 D2 D3 h23).toRingHom.toAlgebra

  have h03 : D0 ≤ D3 := le_trans h02 h23
  have h13 : D1 ≤ D3 := le_trans h12 h23
  letI algB0V0 : Algebra (tensorStage R A 𝒰.A0 D0) (V D3).A0 :=
    ((stgHom R A 𝒰.A0 D3 (V D3).A0 (eV0 D3)).comp (tensorStageMap R A 𝒰.A0 D0 D3 h03).toRingHom).toAlgebra
  letI algB1V1 : Algebra (tensorStage R A 𝒰.A1 D1) (V D3).A1 :=
    ((stgHom R A 𝒰.A1 D3 (V D3).A1 (eV1 D3)).comp (tensorStageMap R A 𝒰.A1 D1 D3 h13).toRingHom).toAlgebra
  letI algV0V01 : Algebra (V D3).A0 (V D3).A01 := (V D3).ρ0.toRingHom.toAlgebra
  letI algV1V01 : Algebra (V D3).A1 (V D3).A01 := (V D3).ρ1.toRingHom.toAlgebra
  letI algB0V01 : Algebra (tensorStage R A 𝒰.A0 D0) (V D3).A01 :=
    ((V D3).ρ0.toRingHom.comp (algebraMap (tensorStage R A 𝒰.A0 D0) (V D3).A0)).toAlgebra
  letI algB1V01 : Algebra (tensorStage R A 𝒰.A1 D1) (V D3).A01 :=
    ((V D3).ρ1.toRingHom.comp (algebraMap (tensorStage R A 𝒰.A1 D1) (V D3).A1)).toAlgebra
  haveI towB0V0V01 : IsScalarTower (tensorStage R A 𝒰.A0 D0) (V D3).A0 (V D3).A01 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI towB1V1V01 : IsScalarTower (tensorStage R A 𝒰.A1 D1) (V D3).A1 (V D3).A01 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI algB''V01 : Algebra (tensorStage R A 𝒰.A01 D3) (V D3).A01 := (stgHom R A 𝒰.A01 D3 (V D3).A01 (eV01 D3)).toAlgebra
  letI algB'V01 : Algebra (tensorStage R A 𝒰.A01 D2) (V D3).A01 :=
    ((stgHom R A 𝒰.A01 D3 (V D3).A01 (eV01 D3)).comp (tensorStageMap R A 𝒰.A01 D2 D3 h23).toRingHom).toAlgebra
  haveI towB'B''V01 : IsScalarTower (tensorStage R A 𝒰.A01 D2) (tensorStage R A 𝒰.A01 D3) (V D3).A01 :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI towB0B'V01 : IsScalarTower (tensorStage R A 𝒰.A0 D0) (tensorStage R A 𝒰.A01 D2) (V D3).A01 := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul γ d =>
      change (V D3).ρ0 (stgHom R A 𝒰.A0 D3 (V D3).A0 (eV0 D3) (tensorStageMap R A 𝒰.A0 D0 D3 h03 (γ ⊗ₜ[R] d))) =
        stgHom R A 𝒰.A01 D3 (V D3).A01 (eV01 D3) (tensorStageMap R A 𝒰.A01 D2 D3 h23
          (Algebra.TensorProduct.map 𝒰.ρ0 (Subalgebra.inclusion (show D0.1 ≤ D2.1 from h02)) (γ ⊗ₜ[R] d)))
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, stgHom_tmul,
        stgHom_tmul, AlgHom.coe_id, id_eq, AlgHom.coe_id, id_eq, hρV0]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  haveI towB1B'V01 : IsScalarTower (tensorStage R A 𝒰.A1 D1) (tensorStage R A 𝒰.A01 D2) (V D3).A01 := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul γ d =>
      change (V D3).ρ1 (stgHom R A 𝒰.A1 D3 (V D3).A1 (eV1 D3) (tensorStageMap R A 𝒰.A1 D1 D3 h13 (γ ⊗ₜ[R] d))) =
        stgHom R A 𝒰.A01 D3 (V D3).A01 (eV01 D3) (tensorStageMap R A 𝒰.A01 D2 D3 h23
          (Algebra.TensorProduct.map 𝒰.ρ1 (Subalgebra.inclusion (show D1.1 ≤ D2.1 from h12)) (γ ⊗ₜ[R] d)))
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, stgHom_tmul,
        stgHom_tmul, AlgHom.coe_id, id_eq, AlgHom.coe_id, id_eq, hρV1]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

  have hrk0 : ∀ (K : Type u) [Field K] [Algebra (V D3).A0 K],
      Module.finrank K (K ⊗[(V D3).A0] ((V D3).A0 ⊗[tensorStage R A 𝒰.A0 D0] L0)) = 1 := by
    intro K _ _
    letI : Algebra (tensorStage R A 𝒰.A0 D0) K := ((algebraMap (V D3).A0 K).comp (algebraMap _ (V D3).A0)).toAlgebra
    haveI : IsScalarTower (tensorStage R A 𝒰.A0 D0) (V D3).A0 K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (V D3).A0 K K L0).finrank_eq]
    exact finrank_baseChange_eq_one_of_invertible L0 K
  have hrk1 : ∀ (K : Type u) [Field K] [Algebra (V D3).A1 K],
      Module.finrank K (K ⊗[(V D3).A1] ((V D3).A1 ⊗[tensorStage R A 𝒰.A1 D1] L1)) = 1 := by
    intro K _ _
    letI : Algebra (tensorStage R A 𝒰.A1 D1) K := ((algebraMap (V D3).A1 K).comp (algebraMap _ (V D3).A1)).toAlgebra
    haveI : IsScalarTower (tensorStage R A 𝒰.A1 D1) (V D3).A1 K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A1 D1) (V D3).A1 K K L1).finrank_eq]
    exact finrank_baseChange_eq_one_of_invertible L1 K
  let κ0 : (V D3).A01 ⊗[(V D3).A0] ((V D3).A0 ⊗[tensorStage R A 𝒰.A0 D0] L0) ≃ₗ[(V D3).A01]
      (V D3).A01 ⊗[tensorStage R A 𝒰.A01 D3]
        (tensorStage R A 𝒰.A01 D3 ⊗[tensorStage R A 𝒰.A01 D2] (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A0 D0] L0)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (V D3).A0 (V D3).A01 (V D3).A01 L0) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (tensorStage R A 𝒰.A01 D2)
      (V D3).A01 (V D3).A01 L0).symm ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A01 D2) (tensorStage R A 𝒰.A01 D3)
      (V D3).A01 (V D3).A01 (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A0 D0] L0)).symm
  let κ1 : (V D3).A01 ⊗[(V D3).A1] ((V D3).A1 ⊗[tensorStage R A 𝒰.A1 D1] L1) ≃ₗ[(V D3).A01]
      (V D3).A01 ⊗[tensorStage R A 𝒰.A01 D3]
        (tensorStage R A 𝒰.A01 D3 ⊗[tensorStage R A 𝒰.A01 D2] (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A1 D1] L1)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A1 D1) (V D3).A1 (V D3).A01 (V D3).A01 L1) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A1 D1) (tensorStage R A 𝒰.A01 D2)
      (V D3).A01 (V D3).A01 L1).symm ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A01 D2) (tensorStage R A 𝒰.A01 D3)
      (V D3).A01 (V D3).A01 (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A1 D1] L1)).symm
  let σV : (V D3).A01 ⊗[(V D3).A0] ((V D3).A0 ⊗[tensorStage R A 𝒰.A0 D0] L0) ≃ₗ[(V D3).A01]
      (V D3).A01 ⊗[(V D3).A1] ((V D3).A1 ⊗[tensorStage R A 𝒰.A1 D1] L1) :=
    κ0 ≪≫ₗ (LinearEquiv.baseChange (tensorStage R A 𝒰.A01 D3) (V D3).A01 _ _ σ3) ≪≫ₗ κ1.symm
  refine ⟨D3, (V D3).A0 ⊗[tensorStage R A 𝒰.A0 D0] L0, inferInstance, inferInstance, inferInstance, inferInstance,
    (V D3).A1 ⊗[tensorStage R A 𝒰.A1 D1] L1, inferInstance, inferInstance, inferInstance, inferInstance,
    hrk0, hrk1, σV, fun S e0 e1 e01 hC0 hC1 => ?_⟩

  haveI : SMulCommClass (tensorStage R A 𝒰.A0 D0) ↥D3.1 (V D3).A0 := smulCommClass_of_algebras _ _ _
  haveI : SMulCommClass (tensorStage R A 𝒰.A0 D0) ↥D3.1 (V D3).A01 := smulCommClass_of_algebras _ _ _
  haveI : SMulCommClass (tensorStage R A 𝒰.A1 D1) ↥D3.1 (V D3).A1 := smulCommClass_of_algebras _ _ _
  haveI : SMulCommClass (V D3).A0 ↥D3.1 (V D3).A01 := smulCommClass_of_algebras _ _ _
  haveI : SMulCommClass (V D3).A1 ↥D3.1 (V D3).A01 := smulCommClass_of_algebras _ _ _
  haveI : SMulCommClass (tensorStage R A 𝒰.A0 D0) A UA.A0 := smulCommClass_of_algebras _ _ _
  haveI : SMulCommClass (tensorStage R A 𝒰.A0 D0) A UA.A01 := smulCommClass_of_algebras _ _ _
  haveI : SMulCommClass (tensorStage R A 𝒰.A1 D1) A UA.A1 := smulCommClass_of_algebras _ _ _
  obtain ⟨Z0', hZ0', hZ0's⟩ := exists_presentEquiv ↥D3.1 A (V D3).A0 UA.A0 (tensorStage R A 𝒰.A0 D0) L0
    (φ0 D3) (eφ0 D3) (heφ0 D3) (by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul γ d =>
        change vtxHom R A 𝒰.A0 UA.A0 eU0 D0 (γ ⊗ₜ[R] d) =
          φ0 D3 (stgHom R A 𝒰.A0 D3 (V D3).A0 (eV0 D3) (tensorStageMap R A 𝒰.A0 D0 D3 h03 (γ ⊗ₜ[R] d)))
        rw [vtxHom_tmul, Algebra.TensorProduct.map_tmul, stgHom_tmul, AlgHom.coe_id, id_eq, hφe0]
        rfl
      | add x y hx hy => simp only [map_add, hx, hy])
  obtain ⟨Z1', hZ1', hZ1's⟩ := exists_presentEquiv ↥D3.1 A (V D3).A1 UA.A1 (tensorStage R A 𝒰.A1 D1) L1
    (φ1 D3) (eφ1 D3) (heφ1 D3) (by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul γ d =>
        change vtxHom R A 𝒰.A1 UA.A1 eU1 D1 (γ ⊗ₜ[R] d) =
          φ1 D3 (stgHom R A 𝒰.A1 D3 (V D3).A1 (eV1 D3) (tensorStageMap R A 𝒰.A1 D1 D3 h13 (γ ⊗ₜ[R] d)))
        rw [vtxHom_tmul, Algebra.TensorProduct.map_tmul, stgHom_tmul, AlgHom.coe_id, id_eq, hφe1]
        rfl
      | add x y hx hy => simp only [map_add, hx, hy])
  obtain ⟨Z01', hZ01', hZ01's⟩ := exists_presentEquiv ↥D3.1 A (V D3).A01 UA.A01 (tensorStage R A 𝒰.A0 D0) L0
    (φ01 D3) (eφ01 D3) (heφ01 D3) (by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul γ d =>
        change UA.ρ0 (vtxHom R A 𝒰.A0 UA.A0 eU0 D0 (γ ⊗ₜ[R] d)) =
          φ01 D3 ((V D3).ρ0 (stgHom R A 𝒰.A0 D3 (V D3).A0 (eV0 D3) (tensorStageMap R A 𝒰.A0 D0 D3 h03 (γ ⊗ₜ[R] d))))
        rw [vtxHom_tmul, Algebra.TensorProduct.map_tmul, stgHom_tmul, AlgHom.coe_id, id_eq, hρV0, hφe01, hρU0]
        rfl
      | add x y hx hy => simp only [map_add, hx, hy])
  let Z0 : A ⊗[↥D3.1] S.M0 ≃ₗ[A] T.M0 :=
    (LinearEquiv.baseChange ↥D3.1 A _ _ (e0.restrictScalars ↥D3.1)) ≪≫ₗ Z0' ≪≫ₗ ι0.restrictScalars A
  let Z1 : A ⊗[↥D3.1] S.M1 ≃ₗ[A] T.M1 :=
    (LinearEquiv.baseChange ↥D3.1 A _ _ (e1.restrictScalars ↥D3.1)) ≪≫ₗ Z1' ≪≫ₗ ι1.restrictScalars A
  let Z01 : A ⊗[↥D3.1] S.M01 ≃ₗ[A] T.M01 :=
    (LinearEquiv.baseChange ↥D3.1 A _ _ (e01.restrictScalars ↥D3.1)) ≪≫ₗ
    (LinearEquiv.baseChange ↥D3.1 A _ _
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (V D3).A0 (V D3).A01 (V D3).A01
        L0).restrictScalars ↥D3.1)) ≪≫ₗ
    Z01' ≪≫ₗ θ0'.restrictScalars A

  have hZ0 : ∀ (a : A) (m : S.M0), Z0 (a ⊗ₜ[↥D3.1] m) = ι0 (Z0' (a ⊗ₜ[↥D3.1] e0 m)) := fun a m => by
    change ι0 (Z0' (LinearEquiv.baseChange ↥D3.1 A _ _ (e0.restrictScalars ↥D3.1) (a ⊗ₜ[↥D3.1] m))) = _
    rw [LinearEquiv.baseChange_tmul]; rfl
  have hZ1 : ∀ (a : A) (m : S.M1), Z1 (a ⊗ₜ[↥D3.1] m) = ι1 (Z1' (a ⊗ₜ[↥D3.1] e1 m)) := fun a m => by
    change ι1 (Z1' (LinearEquiv.baseChange ↥D3.1 A _ _ (e1.restrictScalars ↥D3.1) (a ⊗ₜ[↥D3.1] m))) = _
    rw [LinearEquiv.baseChange_tmul]; rfl
  have hZ01 : ∀ (a : A) (m : S.M01), Z01 (a ⊗ₜ[↥D3.1] m) = θ0' (Z01' (a ⊗ₜ[↥D3.1]
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (V D3).A0 (V D3).A01 (V D3).A01 L0
        (e01 m)))) := fun a m => by
    change θ0' (Z01' (LinearEquiv.baseChange ↥D3.1 A _ _ ((TensorProduct.AlgebraTensorModule.cancelBaseChange
      (tensorStage R A 𝒰.A0 D0) (V D3).A0 (V D3).A01 (V D3).A01 L0).restrictScalars ↥D3.1)
      (LinearEquiv.baseChange ↥D3.1 A _ _ (e01.restrictScalars ↥D3.1) (a ⊗ₜ[↥D3.1] m)))) = _
    rw [LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul]; rfl

  have hθ0' : ∀ (w : UA.A01) (l : L0), θ0' (w ⊗ₜ[tensorStage R A 𝒰.A0 D0] l) =
      w • T.r0 (ι0 ((1 : UA.A0) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l)) := fun w l => by
    change rbc0 (LinearEquiv.baseChange UA.A0 UA.A01 _ _ ι0 ((TensorProduct.AlgebraTensorModule.cancelBaseChange
      (tensorStage R A 𝒰.A0 D0) UA.A0 UA.A01 UA.A01 L0).symm (w ⊗ₜ[tensorStage R A 𝒰.A0 D0] l))) = _
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
      show w ⊗ₜ[UA.A0] ι0 ((1 : UA.A0) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l) =
        w • ((1 : UA.A01) ⊗ₜ[UA.A0] ι0 ((1 : UA.A0) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l)) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, hrbc0]
  have hθ1' : ∀ (w : UA.A01) (l : L1), θ1' (w ⊗ₜ[tensorStage R A 𝒰.A1 D1] l) =
      w • T.r1 (ι1 ((1 : UA.A1) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)) := fun w l => by
    change rbc1 (LinearEquiv.baseChange UA.A1 UA.A01 _ _ ι1 ((TensorProduct.AlgebraTensorModule.cancelBaseChange
      (tensorStage R A 𝒰.A1 D1) UA.A1 UA.A01 UA.A01 L1).symm (w ⊗ₜ[tensorStage R A 𝒰.A1 D1] l))) = _
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
      show w ⊗ₜ[UA.A1] ι1 ((1 : UA.A1) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l) =
        w • ((1 : UA.A01) ⊗ₜ[UA.A1] ι1 ((1 : UA.A1) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, hrbc1]
  refine ⟨{ β0 := Z0, β1 := Z1, β01 := Z01, hr0 := ?_, hr1 := ?_, hs0 := ?_, hs1 := ?_, hs01 := ?_ }⟩
  ·
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, hZ01, hZ0, hC0]
      generalize e0 m = p
      induction p using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul v l =>
        have h1 : (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (V D3).A0 (V D3).A01
            (V D3).A01 L0) ((1 : (V D3).A01) ⊗ₜ[(V D3).A0] (v ⊗ₜ[tensorStage R A 𝒰.A0 D0] l)) =
            ((V D3).ρ0 v) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l := by
          rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]; rfl
        rw [h1, hZ01', hθ0', hZ0',
          show ((a • φ0 D3 v) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l : UA.A0 ⊗[tensorStage R A 𝒰.A0 D0] L0) =
            (a • φ0 D3 v) • ((1 : UA.A0) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l) by
              rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul ι0, T.r0_smul, map_smul UA.ρ0, ← hφρ0]
  ·

    have hφv : ∀ x : tensorStage R A 𝒰.A01 D3,
        φ01 D3 (algebraMap (tensorStage R A 𝒰.A01 D3) (V D3).A01 x) = g'' x := by
      intro x
      rw [hg'']
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul γ d =>
        change φ01 D3 (stgHom R A 𝒰.A01 D3 (V D3).A01 (eV01 D3) (γ ⊗ₜ[R] d)) =
          vtxHom R A 𝒰.A01 UA.A01 eU01 D3 (γ ⊗ₜ[R] d)
        rw [stgHom_tmul, vtxHom_tmul, hφe01]

    have hκ1 : ∀ (v : (V D3).A1) (l : L1), κ1 ((1 : (V D3).A01) ⊗ₜ[(V D3).A1] (v ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)) =
        ((V D3).ρ1 v) ⊗ₜ[tensorStage R A 𝒰.A01 D3] ((1 : tensorStage R A 𝒰.A01 D3) ⊗ₜ[tensorStage R A 𝒰.A01 D2]
          ((1 : tensorStage R A 𝒰.A01 D2) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)) := fun v l => by
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A01 D2) (tensorStage R A 𝒰.A01 D3)
          (V D3).A01 (V D3).A01 (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A1 D1] L1)).symm
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A1 D1) (tensorStage R A 𝒰.A01 D2)
          (V D3).A01 (V D3).A01 L1).symm
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A1 D1) (V D3).A1 (V D3).A01 (V D3).A01 L1)
          ((1 : (V D3).A01) ⊗ₜ[(V D3).A1] (v ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)))) = _
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
      rfl
    have hκ0f : ∀ (w : (V D3).A01) (l : L0), κ0 (w ⊗ₜ[(V D3).A0] ((1 : (V D3).A0) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l)) =
        w ⊗ₜ[tensorStage R A 𝒰.A01 D3] ((1 : tensorStage R A 𝒰.A01 D3) ⊗ₜ[tensorStage R A 𝒰.A01 D2]
          ((1 : tensorStage R A 𝒰.A01 D2) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l)) := fun w l => by
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A01 D2) (tensorStage R A 𝒰.A01 D3)
          (V D3).A01 (V D3).A01 (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A0 D0] L0)).symm
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (tensorStage R A 𝒰.A01 D2)
          (V D3).A01 (V D3).A01 L0).symm
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (V D3).A0 (V D3).A01 (V D3).A01 L0)
          (w ⊗ₜ[(V D3).A0] ((1 : (V D3).A0) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l)))) = _
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    have hκ0 : ∀ (b : tensorStage R A 𝒰.A01 D3) (β : tensorStage R A 𝒰.A01 D2) (l : L0),
        κ0.symm ((1 : (V D3).A01) ⊗ₜ[tensorStage R A 𝒰.A01 D3] (b ⊗ₜ[tensorStage R A 𝒰.A01 D2]
          (β ⊗ₜ[tensorStage R A 𝒰.A0 D0] l))) =
        (algebraMap (tensorStage R A 𝒰.A01 D3) (V D3).A01 (β • b)) ⊗ₜ[(V D3).A0]
          ((1 : (V D3).A0) ⊗ₜ[tensorStage R A 𝒰.A0 D0] l) := fun b β l => by
      rw [LinearEquiv.symm_apply_eq, hκ0f, one_tmul_tmul_tmul]

    have key : ∀ (a : A) (w : (V D3).A01) (y : tensorStage R A 𝒰.A01 D3 ⊗[tensorStage R A 𝒰.A01 D2]
        (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A0 D0] L0)),
        θ0' (Z01' (a ⊗ₜ[↥D3.1] (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0) (V D3).A0
          (V D3).A01 (V D3).A01 L0 (w • κ0.symm ((1 : (V D3).A01) ⊗ₜ[tensorStage R A 𝒰.A01 D3] y))))) =
          (a • φ01 D3 w) • θ0 (g''.toLinearMap.rTensor _ y) := by
      intro a w y
      induction y using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero, smul_zero]
      | add x y hx hy => simp only [tmul_add, map_add, smul_add, hx, hy]
      | tmul b n =>
        induction n using TensorProduct.induction_on with
        | zero => simp only [tmul_zero, map_zero, smul_zero]
        | add x y hx hy => simp only [tmul_add, map_add, smul_add, hx, hy]
        | tmul β l =>
          rw [hκ0, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
            hZ01', hθ0', map_mul, hφv, map_smul g'', LinearMap.rTensor_tmul]
          change _ = (a • φ01 D3 w) • θ0' (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A0 D0)
            (tensorStage R A 𝒰.A01 D2) UA.A01 UA.A01 L0 (g''.toLinearMap b ⊗ₜ[tensorStage R A 𝒰.A01 D2]
              (β ⊗ₜ[tensorStage R A 𝒰.A0 D0] l)))
          rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, hθ0', AlgHom.toLinearMap_apply, smul_smul,
            smul_mul_assoc]

    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, hZ01, hZ1, show e01 (S.r1 m) = σV.symm ((1 : (V D3).A01) ⊗ₜ[(V D3).A1] e1 m) by
        rw [LinearEquiv.eq_symm_apply]; exact hC1 m]
      generalize e1 m = q
      induction q using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul v l =>
        rw [show σV.symm ((1 : (V D3).A01) ⊗ₜ[(V D3).A1] (v ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)) =
            κ0.symm ((LinearEquiv.baseChange (tensorStage R A 𝒰.A01 D3) (V D3).A01 _ _ σ3).symm
              (κ1 ((1 : (V D3).A01) ⊗ₜ[(V D3).A1] (v ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)))) from rfl, hκ1,
          show ((V D3).ρ1 v ⊗ₜ[tensorStage R A 𝒰.A01 D3] ((1 : tensorStage R A 𝒰.A01 D3) ⊗ₜ[tensorStage R A 𝒰.A01 D2]
              ((1 : tensorStage R A 𝒰.A01 D2) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)) : (V D3).A01 ⊗[tensorStage R A 𝒰.A01 D3]
                (tensorStage R A 𝒰.A01 D3 ⊗[tensorStage R A 𝒰.A01 D2] (tensorStage R A 𝒰.A01 D2 ⊗[tensorStage R A 𝒰.A1 D1] L1))) =
            (V D3).ρ1 v • ((1 : (V D3).A01) ⊗ₜ[tensorStage R A 𝒰.A01 D3] ((1 : tensorStage R A 𝒰.A01 D3) ⊗ₜ[tensorStage R A 𝒰.A01 D2]
              ((1 : tensorStage R A 𝒰.A01 D2) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l))) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], LinearEquiv.map_smul,
          show (LinearEquiv.baseChange (tensorStage R A 𝒰.A01 D3) (V D3).A01 _ _ σ3).symm
              ((1 : (V D3).A01) ⊗ₜ[tensorStage R A 𝒰.A01 D3] ((1 : tensorStage R A 𝒰.A01 D3) ⊗ₜ[tensorStage R A 𝒰.A01 D2]
                ((1 : tensorStage R A 𝒰.A01 D2) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l))) =
            (1 : (V D3).A01) ⊗ₜ[tensorStage R A 𝒰.A01 D3] σ3.symm ((1 : tensorStage R A 𝒰.A01 D3) ⊗ₜ[tensorStage R A 𝒰.A01 D2]
                ((1 : tensorStage R A 𝒰.A01 D2) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)) by
            rw [LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul, LinearEquiv.apply_symm_apply],
          LinearEquiv.map_smul, key]

        have hc := hσ3 (σ3.symm ((1 : tensorStage R A 𝒰.A01 D3) ⊗ₜ[tensorStage R A 𝒰.A01 D2]
          ((1 : tensorStage R A 𝒰.A01 D2) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l)))
        rw [LinearEquiv.apply_symm_apply, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
          LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq] at hc
        rw [hc]
        change (a • φ01 D3 ((V D3).ρ1 v)) • θ1' (TensorProduct.AlgebraTensorModule.cancelBaseChange (tensorStage R A 𝒰.A1 D1)
            (tensorStage R A 𝒰.A01 D2) UA.A01 UA.A01 L1 ((1 : UA.A01) ⊗ₜ[tensorStage R A 𝒰.A01 D2]
              ((1 : tensorStage R A 𝒰.A01 D2) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l))) = _
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul, hθ1', one_smul, hZ1',
          show ((a • φ1 D3 v) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l : UA.A1 ⊗[tensorStage R A 𝒰.A1 D1] L1) =
            (a • φ1 D3 v) • ((1 : UA.A1) ⊗ₜ[tensorStage R A 𝒰.A1 D1] l) by
              rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul ι1, T.r1_smul, map_smul UA.ρ1, ← hφρ1]
  ·
    intro s m
    rw [hZ0, hZ0, map_smul, hZ0's, one_smul, map_smul]
  ·
    intro s m
    rw [hZ1, hZ1, map_smul, hZ1's, one_smul, map_smul]
  ·
    intro s m
    rw [hZ01, hZ01, map_smul, map_smul, hZ01's, one_smul, map_smul]

end AbstractSurj
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"

section GeoDict

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover TwoChartCech"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))

set_option maxHeartbeats 3200000 in

theorem cover_ρ0_present (B : Type u) [CommRing B] [Algebra R B]
    (e0 : B ⊗[R] (𝒱.cover c).A0 ≃ₐ[B] ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).A0)
    (e01 : B ⊗[R] (𝒱.cover c).A01 ≃ₐ[B] ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).A01)
    (he0 : ∀ s, e0 ((1 : B) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R B)).app 𝒱.U0).hom s)
    (he01 : ∀ s, e01 ((1 : B) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R B)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s)
    (b : B) (γ : (𝒱.cover c).A0) :
    ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).ρ0 (e0 (b ⊗ₜ[R] γ)) = e01 (b ⊗ₜ[R] (𝒱.cover c).ρ0 γ) := by
  rw [show b ⊗ₜ[R] γ = b • ((1 : B) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    show b ⊗ₜ[R] (𝒱.cover c).ρ0 γ = b • ((1 : B) ⊗ₜ[R] (𝒱.cover c).ρ0 γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, map_smul, map_smul, he0, he01, cover_ρ0_apply, cover_ρ0_apply, Scheme.Hom.app_apply_map]
  rfl

set_option maxHeartbeats 3200000 in
theorem cover_ρ1_present (B : Type u) [CommRing B] [Algebra R B]
    (e1 : B ⊗[R] (𝒱.cover c).A1 ≃ₐ[B] ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).A1)
    (e01 : B ⊗[R] (𝒱.cover c).A01 ≃ₐ[B] ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).A01)
    (he1 : ∀ s, e1 ((1 : B) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R B)).app 𝒱.U1).hom s)
    (he01 : ∀ s, e01 ((1 : B) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R B)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s)
    (b : B) (γ : (𝒱.cover c).A1) :
    ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).ρ1 (e1 (b ⊗ₜ[R] γ)) = e01 (b ⊗ₜ[R] (𝒱.cover c).ρ1 γ) := by
  rw [show b ⊗ₜ[R] γ = b • ((1 : B) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    show b ⊗ₜ[R] (𝒱.cover c).ρ1 γ = b • ((1 : B) ⊗ₜ[R] (𝒱.cover c).ρ1 γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, map_smul, map_smul, he1, he01, cover_ρ1_apply, cover_ρ1_apply, Scheme.Hom.app_apply_map]
  rfl

variable (A : Type u) [CommRing A] [Algebra R A] (D : Subalgebra R A)

noncomputable abbrev φU0 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A0 →+*
    ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0 :=
  ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).appLE (𝒱.pullback c ↥D).U0
    (𝒱.pullback c A).U0 (baseChangeSnd_preimage_U0 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge).hom
noncomputable abbrev φU1 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A1 →+*
    ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1 :=
  ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).appLE (𝒱.pullback c ↥D).U1
    (𝒱.pullback c A).U1 (baseChangeSnd_preimage_U1 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge).hom
noncomputable abbrev φU01 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A01 →+*
    ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A01 :=
  ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).appLE
    ((𝒱.pullback c ↥D).U0 ⊓ (𝒱.pullback c ↥D).U1) ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1)
    (baseChangeSnd_preimage_inf 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge).hom

set_option maxHeartbeats 3200000 in
theorem φU01_ρ0 (s : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A0) :
    φU01 𝒱 c A D (((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).ρ0 s) =
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).ρ0 (φU0 𝒱 c A D s) := by
  rw [cover_ρ0_apply, cover_ρ0_apply]
  exact Scheme.Hom.appLE_apply_map _ _ _ inf_le_left inf_le_left s

set_option maxHeartbeats 3200000 in
theorem φU01_ρ1 (s : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A1) :
    φU01 𝒱 c A D (((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).ρ1 s) =
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).ρ1 (φU1 𝒱 c A D s) := by
  rw [cover_ρ1_apply, cover_ρ1_apply]
  exact Scheme.Hom.appLE_apply_map _ _ _ inf_le_right inf_le_right s

set_option maxHeartbeats 3200000 in
theorem φU0_present
    (eD : ↥D ⊗[R] (𝒱.cover c).A0 ≃ₐ[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A0)
    (heD : ∀ s, eD ((1 : ↥D) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R ↥D)).app 𝒱.U0).hom s)
    (eA : A ⊗[R] (𝒱.cover c).A0 ≃ₐ[A] ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0)
    (heA : ∀ s, eA ((1 : A) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R A)).app 𝒱.U0).hom s)
    (eφ : A ⊗[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A0 ≃ₐ[A]
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0)
    (heφ : ∀ s, eφ ((1 : A) ⊗ₜ[↥D] s) = φU0 𝒱 c A D s)
    (d : ↥D) (γ : (𝒱.cover c).A0) :
    φU0 𝒱 c A D (eD (d ⊗ₜ[R] γ)) = eA ((d : A) ⊗ₜ[R] γ) := by

  have hsc : φU0 𝒱 c A D (algebraMap ↥D _ d) = algebraMap A _ (d : A) := by
    rw [← heφ, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def, smul_eq_mul, mul_one,
      show ((d : A) ⊗ₜ[↥D] (1 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A0)) =
        algebraMap A _ (d : A) from rfl, AlgEquiv.commutes]

  have hfn : φU0 𝒱 c A D (((Limits.pullback.fst c (specMap R ↥D)).app 𝒱.U0).hom γ) =
      ((Limits.pullback.fst c (specMap R A)).app 𝒱.U0).hom γ := by
    have h := Scheme.Hom.appLE_app_apply_of_comp_eq
      (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A)))
      (Limits.pullback.fst c (specMap R ↥D)) (Limits.pullback.fst c (specMap R A))
      (baseChangeSnd_fst c (stageHom R (IsScalarTower.toAlgHom R ↥D A))) (𝒱.U0) ((𝒱.pullback c A).U0)
      (baseChangeSnd_preimage_U0 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge γ
    rw [Scheme.Hom.app_eq_appLE (Limits.pullback.fst c (specMap R A))]
    exact h
  rw [show d ⊗ₜ[R] γ = d • ((1 : ↥D) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    show (d : A) ⊗ₜ[R] γ = (d : A) • ((1 : A) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul eD, map_smul eA, heD, heA, Algebra.smul_def, Algebra.smul_def, map_mul, hsc, hfn]

set_option maxHeartbeats 3200000 in
theorem φU1_present
    (eD : ↥D ⊗[R] (𝒱.cover c).A1 ≃ₐ[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A1)
    (heD : ∀ s, eD ((1 : ↥D) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R ↥D)).app 𝒱.U1).hom s)
    (eA : A ⊗[R] (𝒱.cover c).A1 ≃ₐ[A] ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1)
    (heA : ∀ s, eA ((1 : A) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R A)).app 𝒱.U1).hom s)
    (eφ : A ⊗[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A1 ≃ₐ[A]
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1)
    (heφ : ∀ s, eφ ((1 : A) ⊗ₜ[↥D] s) = φU1 𝒱 c A D s)
    (d : ↥D) (γ : (𝒱.cover c).A1) :
    φU1 𝒱 c A D (eD (d ⊗ₜ[R] γ)) = eA ((d : A) ⊗ₜ[R] γ) := by

  have hsc : φU1 𝒱 c A D (algebraMap ↥D _ d) = algebraMap A _ (d : A) := by
    rw [← heφ, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def, smul_eq_mul, mul_one,
      show ((d : A) ⊗ₜ[↥D] (1 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A1)) =
        algebraMap A _ (d : A) from rfl, AlgEquiv.commutes]

  have hfn : φU1 𝒱 c A D (((Limits.pullback.fst c (specMap R ↥D)).app 𝒱.U1).hom γ) =
      ((Limits.pullback.fst c (specMap R A)).app 𝒱.U1).hom γ := by
    have h := Scheme.Hom.appLE_app_apply_of_comp_eq
      (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A)))
      (Limits.pullback.fst c (specMap R ↥D)) (Limits.pullback.fst c (specMap R A))
      (baseChangeSnd_fst c (stageHom R (IsScalarTower.toAlgHom R ↥D A))) (𝒱.U1) ((𝒱.pullback c A).U1)
      (baseChangeSnd_preimage_U1 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge γ
    rw [Scheme.Hom.app_eq_appLE (Limits.pullback.fst c (specMap R A))]
    exact h
  rw [show d ⊗ₜ[R] γ = d • ((1 : ↥D) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    show (d : A) ⊗ₜ[R] γ = (d : A) • ((1 : A) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul eD, map_smul eA, heD, heA, Algebra.smul_def, Algebra.smul_def, map_mul, hsc, hfn]

set_option maxHeartbeats 3200000 in
theorem φU01_present
    (eD : ↥D ⊗[R] (𝒱.cover c).A01 ≃ₐ[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A01)
    (heD : ∀ s, eD ((1 : ↥D) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R ↥D)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s)
    (eA : A ⊗[R] (𝒱.cover c).A01 ≃ₐ[A] ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A01)
    (heA : ∀ s, eA ((1 : A) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s)
    (eφ : A ⊗[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A01 ≃ₐ[A]
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A01)
    (heφ : ∀ s, eφ ((1 : A) ⊗ₜ[↥D] s) = φU01 𝒱 c A D s)
    (d : ↥D) (γ : (𝒱.cover c).A01) :
    φU01 𝒱 c A D (eD (d ⊗ₜ[R] γ)) = eA ((d : A) ⊗ₜ[R] γ) := by

  have hsc : φU01 𝒱 c A D (algebraMap ↥D _ d) = algebraMap A _ (d : A) := by
    rw [← heφ, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def, smul_eq_mul, mul_one,
      show ((d : A) ⊗ₜ[↥D] (1 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A01)) =
        algebraMap A _ (d : A) from rfl, AlgEquiv.commutes]

  have hfn : φU01 𝒱 c A D (((Limits.pullback.fst c (specMap R ↥D)).app (𝒱.U0 ⊓ 𝒱.U1)).hom γ) =
      ((Limits.pullback.fst c (specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom γ := by
    have h := Scheme.Hom.appLE_app_apply_of_comp_eq
      (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A)))
      (Limits.pullback.fst c (specMap R ↥D)) (Limits.pullback.fst c (specMap R A))
      (baseChangeSnd_fst c (stageHom R (IsScalarTower.toAlgHom R ↥D A))) ((𝒱.U0 ⊓ 𝒱.U1)) (((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1))
      (baseChangeSnd_preimage_inf 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge γ
    rw [Scheme.Hom.app_eq_appLE (Limits.pullback.fst c (specMap R A))]
    exact h
  rw [show d ⊗ₜ[R] γ = d • ((1 : ↥D) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    show (d : A) ⊗ₜ[R] γ = (d : A) • ((1 : A) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul eD, map_smul eA, heD, heA, Algebra.smul_def, Algebra.smul_def, map_mul, hsc, hfn]

end GeoDict
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"

section Final

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover TwoChartCech AlgebraicGeometry.FGSubalgebra"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem exists_fg_nonempty_iso_pullbackAlong
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (M : RigidifiedLineBundle c ε (specMap R A)) :
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (M₀ : RigidifiedLineBundle c ε (specMap R A₀)),
      Nonempty ((M₀.pullbackAlong (stageHom R A₀.val)).L ≅ M.L) := by
  classical

  obtain ⟨hP0, hF0, hrkT0, hP1, hF1, hrkT1, -, -, -⟩ :=
    sectionsOf_isInvertible_projective_finite_finrank (𝒱.pullback c A) (Limits.pullback.snd c (specMap R A)) M.L M.isInvertible
  haveI := hP0; haveI := hF0; haveI := hP1; haveI := hF1
  haveI : Module.Invertible ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0
      ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (specMap R A)) M.L).M0 :=
    Module.Invertible.of_projective_of_forall_finrank_eq_one _ hrkT0
  haveI : Module.Invertible ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1
      ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (specMap R A)) M.L).M1 :=
    Module.Invertible.of_projective_of_forall_finrank_eq_one _ hrkT1
  obtain ⟨rbc0, rbc1, hrbc0, hrbc1⟩ := exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
    (𝒱.pullback c A) (Limits.pullback.snd c (specMap R A)) M.L M.isInvertible

  obtain ⟨eU0, eU1, eU01, -, -, heU0, heU1, heU01, -, -⟩ := exists_baseChangeIsos_structureSheaf 𝒱 c A
  choose eV0 eV1 eV01 _eH0 _eH1 heV0 heV1 heV01 _h4 _h5 using
    fun D : FGSubalgebra R A => exists_baseChangeIsos_structureSheaf 𝒱 c ↥D.1
  choose eφ0 eφ1 eφ01 heφ0 heφ1 heφ01 using
    fun D : FGSubalgebra R A => exists_stage_baseChangeIsos_structureSheaf 𝒱 c ↥D.1 A

  obtain ⟨D, P0, _, _, _, _, P1, _, _, _, _, hrk0, hrk1, σ, hZ⟩ := exists_fg_gluingData R A (𝒱.cover c)
    ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A)))
    ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (specMap R A)) M.L)
    eU0 eU1 eU01 (cover_ρ0_present 𝒱 c A eU0 eU01 heU0 heU01) (cover_ρ1_present 𝒱 c A eU1 eU01 heU1 heU01)
    rbc0 hrbc0 rbc1 hrbc1
    (fun D => (𝒱.pullback c ↥D.1).cover (Limits.pullback.snd c (specMap R ↥D.1))) eV0 eV1 eV01
    (fun D => cover_ρ0_present 𝒱 c ↥D.1 (eV0 D) (eV01 D) (heV0 D) (heV01 D))
    (fun D => cover_ρ1_present 𝒱 c ↥D.1 (eV1 D) (eV01 D) (heV1 D) (heV01 D))
    (fun D => φU0 𝒱 c A D.1) (fun D => φU1 𝒱 c A D.1) (fun D => φU01 𝒱 c A D.1)
    eφ0 heφ0 eφ1 heφ1 eφ01 heφ01
    (fun D => φU01_ρ0 𝒱 c A D.1) (fun D => φU01_ρ1 𝒱 c A D.1)
    (fun D => φU0_present 𝒱 c A D.1 (eV0 D) (heV0 D) eU0 heU0 (eφ0 D) (heφ0 D))
    (fun D => φU1_present 𝒱 c A D.1 (eV1 D) (heV1 D) eU1 heU1 (eφ1 D) (heφ1 D))
    (fun D => φU01_present 𝒱 c A D.1 (eV01 D) (heV01 D) eU01 heU01 (eφ01 D) (heφ01 D))

  obtain ⟨L, hL, e0, e1, e01, hC0, hC1⟩ := exists_isInvertible_sectionsOf_equiv_of_projective (𝒱.pullback c ↥D.1)
    (Limits.pullback.snd c (specMap R ↥D.1)) P0 P1 hrk0 hrk1 σ
  obtain ⟨β'⟩ := hZ ((𝒱.pullback c ↥D.1).sectionsOf (Limits.pullback.snd c (specMap R ↥D.1)) L) e0 e1 e01 hC0 hC1

  obtain ⟨γ0, γ1, γ01, gr0, gr1, -, -, -, gs0, gs1, gs01⟩ :=
    exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c ↥D.1 A L hL.1
  let β : ChartBC (k := ↥D.1) (A' := A) (φU0 𝒱 c A D.1) (φU1 𝒱 c A D.1) (φU01 𝒱 c A D.1)
      ((𝒱.pullback c ↥D.1).sectionsOf (Limits.pullback.snd c (specMap R ↥D.1)) L)
      ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (specMap R A))
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D.1 A)))).obj L)) :=
    ⟨γ0, γ1, γ01, gr0, gr1, gs0, gs1, gs01⟩
  obtain ⟨E0, E1, E01, hE0, hE1⟩ := ChartBC.exists_chartIso_of_intertwines β β'
    (mem_span_range_of_algEquiv (eφ0 D) _ (heφ0 D)) (mem_span_range_of_algEquiv (eφ1 D) _ (heφ1 D))
    (mem_span_range_of_algEquiv (eφ01 D) _ (heφ01 D))
    (LinearEquiv.refl _ _) (LinearEquiv.refl _ _) (LinearEquiv.refl _ _) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
  obtain ⟨eL⟩ := nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible (𝒱.pullback c A)
    (Limits.pullback.snd c (specMap R A)) _ _ (hL.pullback _) M.isInvertible E0 E1 E01 hE0 hE1

  have hval : IsScalarTower.toAlgHom R ↥D.1 A = D.1.val := AlgHom.ext fun _ => rfl
  rw [hval] at eL
  refine ⟨D.1, D.2, RigidifiedLineBundle.ofInvertible L hL, ?_⟩
  obtain ⟨i1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) (stageHom R D.1.val) hL
  obtain ⟨i2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hL.pullback (RelPicard.baseChangeSnd c (stageHom R D.1.val))) M.isInvertible eL
  obtain ⟨i3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified (ε := ε) M
  exact ⟨i1 ≪≫ i2 ≪≫ i3⟩

end Final
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"

end AlgebraicGeometry.RelPicard.LFP
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard.LFP"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (M : RigidifiedLineBundle c ε (Scheme.TwoAffineOpenCover.specMap R A)) :
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (M₀ : RigidifiedLineBundle c ε (Scheme.TwoAffineOpenCover.specMap R A₀)),
      Nonempty ((M₀.pullbackAlong (RelPicard.LFP.stageHom R A₀.val)).L ≅ M.L) :=
  AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong R 𝒱 c ε A M

end S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong (solution)
