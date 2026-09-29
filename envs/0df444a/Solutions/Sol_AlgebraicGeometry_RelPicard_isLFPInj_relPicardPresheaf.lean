-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isLFPInj_relPicardPresheaf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3cc44e5f-e565-5b3f-8091-ffe40baad621

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_FGSubalgebraTensorStage
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_Module_IsDirectLimit_exists_linearEquiv_of_finitePresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.mapPresheaf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover AffineLimit.IsLFPInj FGSubalgebra.tensorStage FGSubalgebra.tensorStageMap FGSubalgebra.tensorStageToColimit FGSubalgebra.tensorStageToColimit_comp FGSubalgebra.tensorStageToColimit_surj FGSubalgebra.tensorStageToColimit_zero FGSubalgebra RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.setoid relPicardPresheaf LFP.stageHom"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom stageHom_val"
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem exists_sectionsOf_linearEquiv_of_iso
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {L L' : X.Modules} (ψ : L ≅ L') :
    ∃ (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.sectionsOf c L').M0)
      (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.sectionsOf c L').M1)
      (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.sectionsOf c L').M01),
      (∀ m, e01 ((𝒱.sectionsOf c L).r0 m) = (𝒱.sectionsOf c L').r0 (e0 m)) ∧
      (∀ m, e01 ((𝒱.sectionsOf c L).r1 m) = (𝒱.sectionsOf c L').r1 (e1 m)) ∧
      (∀ m, e0 m = (ψ.hom.app 𝒱.U0).hom m) ∧ (∀ m, e1 m = (ψ.hom.app 𝒱.U1).hom m) ∧
      (∀ m, e01 m = (ψ.hom.app (𝒱.U0 ⊓ 𝒱.U1)).hom m) := by

  let eU : ∀ U : X.Opens, Γ(L, U) ≃ₗ[Γ(X, U)] Γ(L', U) := fun U =>
    { toFun := fun m => (ψ.hom.app U).hom m
      invFun := fun m => (ψ.inv.app U).hom m
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r m => Scheme.Modules.Hom.app_smul ψ.hom r m
      left_inv := fun m => by
        change (ψ.hom.app U ≫ ψ.inv.app U).hom m = m
        rw [← Scheme.Modules.Hom.comp_app, ψ.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
      right_inv := fun m => by
        change (ψ.inv.app U ≫ ψ.hom.app U).hom m = m
        rw [← Scheme.Modules.Hom.comp_app, ψ.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }

  have nat : ∀ {U V : X.Opens} (i : V ⟶ U) (m : Γ(L, U)),
      (ψ.hom.app V).hom (L.presheaf.map i.op m) = L'.presheaf.map i.op ((ψ.hom.app U).hom m) := by
    intro U V i m
    have := congr($((Scheme.Modules.Hom.mapPresheaf ψ.hom).naturality i.op) m)
    simp only [Scheme.Modules.mapPresheaf_app, CategoryTheory.ConcreteCategory.comp_apply] at this
    exact this
  refine ⟨eU 𝒱.U0, eU 𝒱.U1, eU (𝒱.U0 ⊓ 𝒱.U1), ?_, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · intro m; exact nat (homOfLE inf_le_left) m
  · intro m; exact nat (homOfLE inf_le_right) m

end AlgebraicGeometry.RelPicard.LFP

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.mapPresheaf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover AffineLimit.IsLFPInj FGSubalgebra.tensorStage FGSubalgebra.tensorStageMap FGSubalgebra.tensorStageToColimit FGSubalgebra.tensorStageToColimit_comp FGSubalgebra.tensorStageToColimit_surj FGSubalgebra.tensorStageToColimit_zero FGSubalgebra RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.setoid relPicardPresheaf LFP.stageHom"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom stageHom_val"
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

section FG

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  {N : Type*} [AddCommGroup N] [Module k N]

theorem exists_fg_le_forall_rTensor_inclusion_eq (D : Subalgebra k A) (hD : D.FG)
    {X : Type*} (S : Finset X) (t t' : X → ↥D ⊗[k] N)
    (h : ∀ x ∈ S, D.val.toLinearMap.rTensor N (t x) = D.val.toLinearMap.rTensor N (t' x)) :
    ∃ (D' : Subalgebra k A) (hDD' : D ≤ D'), D'.FG ∧
      ∀ x ∈ S, (Subalgebra.inclusion hDD').toLinearMap.rTensor N (t x) =
        (Subalgebra.inclusion hDD').toLinearMap.rTensor N (t' x) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨D, le_rfl, hD, fun x hx => (Finset.notMem_empty x hx).elim⟩
  | insert x₀ S hx₀ ih =>
    obtain ⟨D', hDD', hD', hS⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))

    have hval : D'.val.comp (Subalgebra.inclusion hDD') = D.val := by ext; rfl
    have h₀ : D'.val.toLinearMap.rTensor N ((Subalgebra.inclusion hDD').toLinearMap.rTensor N (t x₀)) =
        D'.val.toLinearMap.rTensor N ((Subalgebra.inclusion hDD').toLinearMap.rTensor N (t' x₀)) := by
      simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap, hval]
      exact h x₀ (Finset.mem_insert_self x₀ S)
    obtain ⟨D'', hD'D'', hD'', h₀'⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hD' h₀
    refine ⟨D'', hDD'.trans hD'D'', hD'', fun x hx => ?_⟩
    have hincl : (Subalgebra.inclusion hD'D'').comp (Subalgebra.inclusion hDD') =
        Subalgebra.inclusion (hDD'.trans hD'D'') := by ext; rfl
    rw [← hincl, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h₀'
    · rw [hS x hx]

end FG

section System

variable (k : Type u) [CommRing k] (A : Type u) [CommRing A] [Algebra k A]
  (Γ : Type u) [CommRing Γ] [Algebra k Γ]

variable {k A Γ}
variable {P : Type w} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {Q : Type w} [AddCommGroup Q] [Module Γ Q] [Module k Q] [IsScalarTower k Γ Q]

theorem exists_fg_linearEquiv_of_intertwines [Module.FinitePresentation Γ P] [Module.FinitePresentation Γ Q]
    (e : A ⊗[k] P ≃ₗ[A] A ⊗[k] Q) (he : Intertwines (_root_.id : Γ → Γ) (e : A ⊗[k] P →ₗ[A] A ⊗[k] Q)) :
    ∃ (D : Subalgebra k A) (_ : D.FG) (eD : ↥D ⊗[k] P ≃ₗ[↥D] ↥D ⊗[k] Q),
      Intertwines (_root_.id : Γ → Γ) (eD : ↥D ⊗[k] P →ₗ[↥D] ↥D ⊗[k] Q) ∧
      ∀ x, D.val.toLinearMap.rTensor Q (eD x) = e (D.val.toLinearMap.rTensor P x) := by
  obtain ⟨D, eD', hsq⟩ := Module.IsDirectLimit.exists_linearEquiv_of_finitePresentation
    (FGSubalgebra.tensorStage k A Γ) (FGSubalgebra.tensorStageMap k A Γ) (Γ ⊗[k] A)
    (FGSubalgebra.tensorStageToColimit k A Γ) (FGSubalgebra.tensorStageToColimit_comp k A Γ)
    (FGSubalgebra.tensorStageToColimit_surj k A Γ) (FGSubalgebra.tensorStageToColimit_zero k A Γ) P Q
    (toOrientEquiv e he)
  refine ⟨D.1, D.2, fromOrientEquiv eD', intertwines_fromOrient _, fun y => ?_⟩

  have := LinearMap.congr_fun hsq ((orient k Γ (↥D.1) P).symm y)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    toOrientEquiv_apply] at this

  rw [fromOrientEquiv_apply, ← orient_rTensor_map k Γ (↥D.1) Q D.1.val, ← this, LinearEquiv.apply_symm_apply,
    orient_rTensor_map, LinearEquiv.apply_symm_apply]

end System

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

section Descent

open TwoChartCech

variable {k : Type u} [CommRing k]

theorem push_rel {A A' A'' : Type*} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A'] [CommRing A'']
    [Algebra k A''] (h : A' →ₐ[k] A'') (v' : A' →ₐ[k] A) (v'' : A'' →ₐ[k] A) (hv : v''.comp h = v')
    {P Q : Type*} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (E : A ⊗[k] P →ₗ[A] A ⊗[k] Q)
    (hf : ∀ x, v'.toLinearMap.rTensor Q (f x) = E (v'.toLinearMap.rTensor P x)) (y : A'' ⊗[k] P) :
    v''.toLinearMap.rTensor Q (push h f y) = E (v''.toLinearMap.rTensor P y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [push_tmul, rTensor_smul', ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap, hv,
      hf, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
      map_one, tmul_eq_smul_one_tmul k A (v'' a) m, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {A : Type u} [CommRing A] [Algebra k A] {𝒰 : Cover.{u, u} k} {S S' : Sections.{u, u, w} 𝒰}

set_option maxHeartbeats 6400000 in

theorem exists_fg_descent
    [Module.FinitePresentation 𝒰.A0 S.M0] [Module.FinitePresentation 𝒰.A1 S.M1]
    [Module.FinitePresentation 𝒰.A01 S.M01] [Module.FinitePresentation 𝒰.A0 S'.M0]
    [Module.FinitePresentation 𝒰.A1 S'.M1] [Module.FinitePresentation 𝒰.A01 S'.M01]
    (e0 : A ⊗[k] S.M0 ≃ₗ[A] A ⊗[k] S'.M0) (e1 : A ⊗[k] S.M1 ≃ₗ[A] A ⊗[k] S'.M1)
    (e01 : A ⊗[k] S.M01 ≃ₗ[A] A ⊗[k] S'.M01)
    (he0 : Intertwines (_root_.id : 𝒰.A0 → 𝒰.A0) (e0 : A ⊗[k] S.M0 →ₗ[A] A ⊗[k] S'.M0))
    (he1 : Intertwines (_root_.id : 𝒰.A1 → 𝒰.A1) (e1 : A ⊗[k] S.M1 →ₗ[A] A ⊗[k] S'.M1))
    (he01 : Intertwines (_root_.id : 𝒰.A01 → 𝒰.A01) (e01 : A ⊗[k] S.M01 →ₗ[A] A ⊗[k] S'.M01))
    (hsq0 : ∀ x, e01 (S.r0.baseChange A x) = S'.r0.baseChange A (e0 x))
    (hsq1 : ∀ x, e01 (S.r1.baseChange A x) = S'.r1.baseChange A (e1 x)) :
    ∃ (D : Subalgebra k A) (_ : D.FG) (f0 : ↥D ⊗[k] S.M0 ≃ₗ[↥D] ↥D ⊗[k] S'.M0)
      (f1 : ↥D ⊗[k] S.M1 ≃ₗ[↥D] ↥D ⊗[k] S'.M1) (f01 : ↥D ⊗[k] S.M01 ≃ₗ[↥D] ↥D ⊗[k] S'.M01),
      Intertwines (_root_.id : 𝒰.A0 → 𝒰.A0) (f0 : ↥D ⊗[k] S.M0 →ₗ[↥D] ↥D ⊗[k] S'.M0) ∧
      Intertwines (_root_.id : 𝒰.A1 → 𝒰.A1) (f1 : ↥D ⊗[k] S.M1 →ₗ[↥D] ↥D ⊗[k] S'.M1) ∧
      Intertwines (_root_.id : 𝒰.A01 → 𝒰.A01) (f01 : ↥D ⊗[k] S.M01 →ₗ[↥D] ↥D ⊗[k] S'.M01) ∧
      (∀ x, f01 (S.r0.baseChange ↥D x) = S'.r0.baseChange ↥D (f0 x)) ∧
      (∀ x, f01 (S.r1.baseChange ↥D x) = S'.r1.baseChange ↥D (f1 x)) := by
  classical

  obtain ⟨D0, hD0, g0, hg0, hg0e⟩ := exists_fg_linearEquiv_of_intertwines e0 he0
  obtain ⟨D1, hD1, g1, hg1, hg1e⟩ := exists_fg_linearEquiv_of_intertwines e1 he1
  obtain ⟨D01, hD01, g01, hg01, hg01e⟩ := exists_fg_linearEquiv_of_intertwines e01 he01

  let D' : Subalgebra k A := D0 ⊔ D1 ⊔ D01
  have hD' : D'.FG := (hD0.sup hD1).sup hD01
  have h0 : D0 ≤ D' := le_sup_left.trans le_sup_left
  have h1 : D1 ≤ D' := le_sup_right.trans le_sup_left
  have h01 : D01 ≤ D' := le_sup_right
  clear_value D'
  let p0 := pushEquiv (P := S.M0) (Q := S'.M0) (Subalgebra.inclusion h0) g0
  let p1 := pushEquiv (P := S.M1) (Q := S'.M1) (Subalgebra.inclusion h1) g1
  let p01 := pushEquiv (P := S.M01) (Q := S'.M01) (Subalgebra.inclusion h01) g01
  have hp0 : Intertwines (_root_.id : 𝒰.A0 → 𝒰.A0) (p0 : ↥D' ⊗[k] S.M0 →ₗ[↥D'] ↥D' ⊗[k] S'.M0) := hg0.push _
  have hp1 : Intertwines (_root_.id : 𝒰.A1 → 𝒰.A1) (p1 : ↥D' ⊗[k] S.M1 →ₗ[↥D'] ↥D' ⊗[k] S'.M1) := hg1.push _
  have hp01 : Intertwines (_root_.id : 𝒰.A01 → 𝒰.A01) (p01 : ↥D' ⊗[k] S.M01 →ₗ[↥D'] ↥D' ⊗[k] S'.M01) :=
    hg01.push _
  have hp0e : ∀ y, D'.val.toLinearMap.rTensor S'.M0 (p0 y) = e0 (D'.val.toLinearMap.rTensor S.M0 y) :=
    push_rel (Subalgebra.inclusion h0) D0.val D'.val (by ext; rfl) _ _ hg0e
  have hp1e : ∀ y, D'.val.toLinearMap.rTensor S'.M1 (p1 y) = e1 (D'.val.toLinearMap.rTensor S.M1 y) :=
    push_rel (Subalgebra.inclusion h1) D1.val D'.val (by ext; rfl) _ _ hg1e
  have hp01e : ∀ y, D'.val.toLinearMap.rTensor S'.M01 (p01 y) = e01 (D'.val.toLinearMap.rTensor S.M01 y) :=
    push_rel (Subalgebra.inclusion h01) D01.val D'.val (by ext; rfl) _ _ hg01e
  clear_value p0 p1 p01
  clear hg0e hg1e hg01e hg0 hg1 hg01

  obtain ⟨G0, hG0⟩ := Module.Finite.fg_top (R := 𝒰.A0) (M := S.M0)
  obtain ⟨G1, hG1⟩ := Module.Finite.fg_top (R := 𝒰.A1) (M := S.M1)

  let t : S.M0 ⊕ S.M1 → ↥D' ⊗[k] S'.M01 :=
    Sum.elim (fun m => p01 (S.r0.baseChange ↥D' ((1 : ↥D') ⊗ₜ[k] m)))
      (fun m => p01 (S.r1.baseChange ↥D' ((1 : ↥D') ⊗ₜ[k] m)))
  let t' : S.M0 ⊕ S.M1 → ↥D' ⊗[k] S'.M01 :=
    Sum.elim (fun m => S'.r0.baseChange ↥D' (p0 ((1 : ↥D') ⊗ₜ[k] m)))
      (fun m => S'.r1.baseChange ↥D' (p1 ((1 : ↥D') ⊗ₜ[k] m)))
  have ht : ∀ x ∈ G0.disjSum G1, D'.val.toLinearMap.rTensor S'.M01 (t x) = D'.val.toLinearMap.rTensor S'.M01 (t' x) := by
    rintro (m | m) -
    · simp only [t, t', Sum.elim_inl]
      rw [hp01e, rTensor_baseChange, hsq0, rTensor_baseChange, hp0e]
    · simp only [t, t', Sum.elim_inr]
      rw [hp01e, rTensor_baseChange, hsq1, rTensor_baseChange, hp1e]
  obtain ⟨D, hD'D, hD, hsep⟩ := exists_fg_le_forall_rTensor_inclusion_eq D' hD' (G0.disjSum G1) t t' ht

  clear ht hp0e hp1e hp01e
  let ι := Subalgebra.inclusion hD'D
  refine ⟨D, hD, pushEquiv ι p0, pushEquiv ι p1, pushEquiv ι p01, ?_, ?_, ?_, ?_, ?_⟩
  · rw [coe_pushEquiv]; exact hp0.push ι
  · rw [coe_pushEquiv]; exact hp1.push ι
  · rw [coe_pushEquiv]; exact hp01.push ι
  ·
    have key : (pushEquiv ι p01 : ↥D ⊗[k] S.M01 →ₗ[↥D] ↥D ⊗[k] S'.M01) ∘ₗ S.r0.baseChange ↥D =
        S'.r0.baseChange ↥D ∘ₗ (pushEquiv ι p0 : ↥D ⊗[k] S.M0 →ₗ[↥D] ↥D ⊗[k] S'.M0) := by
      refine linearMap_ext_of_span _ _ (fun s => actR k ↥D (𝒰.ρ0 s)) (fun s x => ?_) (fun s x => ?_) ↑G0 hG0
        (fun m hm => ?_)
      · rw [LinearMap.comp_apply, LinearMap.comp_apply, Intertwines.baseChange 𝒰.ρ0 S.r0 S.r0_smul, coe_pushEquiv,
          (hp01.push ι)]
        rfl
      · rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_pushEquiv, (hp0.push ι),
          Intertwines.baseChange 𝒰.ρ0 S'.r0 S'.r0_smul]
        rfl
      · have := hsep (Sum.inl m) (Finset.inl_mem_disjSum.mpr hm)
        simp only [t, t', Sum.elim_inl, LinearMap.baseChange_tmul] at this
        rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_pushEquiv, coe_pushEquiv, LinearMap.baseChange_tmul,
          push_tmul, one_smul, push_tmul, one_smul, ← rTensor_baseChange]
        exact this
    exact fun x => LinearMap.congr_fun key x
  · have key : (pushEquiv ι p01 : ↥D ⊗[k] S.M01 →ₗ[↥D] ↥D ⊗[k] S'.M01) ∘ₗ S.r1.baseChange ↥D =
        S'.r1.baseChange ↥D ∘ₗ (pushEquiv ι p1 : ↥D ⊗[k] S.M1 →ₗ[↥D] ↥D ⊗[k] S'.M1) := by
      refine linearMap_ext_of_span _ _ (fun s => actR k ↥D (𝒰.ρ1 s)) (fun s x => ?_) (fun s x => ?_) ↑G1 hG1
        (fun m hm => ?_)
      · rw [LinearMap.comp_apply, LinearMap.comp_apply, Intertwines.baseChange 𝒰.ρ1 S.r1 S.r1_smul, coe_pushEquiv,
          (hp01.push ι)]
        rfl
      · rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_pushEquiv, (hp1.push ι),
          Intertwines.baseChange 𝒰.ρ1 S'.r1 S'.r1_smul]
        rfl
      · have := hsep (Sum.inr m) (Finset.inr_mem_disjSum.mpr hm)
        simp only [t, t', Sum.elim_inr, LinearMap.baseChange_tmul] at this
        rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_pushEquiv, coe_pushEquiv, LinearMap.baseChange_tmul,
          push_tmul, one_smul, push_tmul, one_smul, ← rTensor_baseChange]
        exact this
    exact fun x => LinearMap.congr_fun key x

end Descent
end AlgebraicGeometry.RelPicard.LFP
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.mapPresheaf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover AffineLimit.IsLFPInj FGSubalgebra.tensorStage FGSubalgebra.tensorStageMap FGSubalgebra.tensorStageToColimit FGSubalgebra.tensorStageToColimit_comp FGSubalgebra.tensorStageToColimit_surj FGSubalgebra.tensorStageToColimit_zero FGSubalgebra RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.setoid relPicardPresheaf LFP.stageHom"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom stageHom_val"
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover TwoChartCech"

theorem fg_restrictScalars_of_fg {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (A₀ : Subalgebra R A) (hA₀ : A₀.FG) (D : Subalgebra ↥A₀ A) (hD : D.FG) : (D.restrictScalars R).FG := by
  classical
  obtain ⟨t, rfl⟩ := hA₀
  obtain ⟨s, rfl⟩ := hD
  exact ⟨t ∪ s, by rw [Finset.coe_union, Algebra.adjoin_union_eq_adjoin_adjoin]⟩

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_fg_le_nonempty_iso_pullbackAlong
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (hA₀ : A₀.FG)
    (M M' : RigidifiedLineBundle c ε (specMap R A₀))
    (h : Nonempty ((M.pullbackAlong (stageHom R A₀.val)).L ≅ (M'.pullbackAlong (stageHom R A₀.val)).L)) :
    ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (hle : A₀ ≤ A₁),
      Nonempty ((M.pullbackAlong (stageHom R (Subalgebra.inclusion hle))).L ≅
        (M'.pullbackAlong (stageHom R (Subalgebra.inclusion hle))).L) := by
  classical

  obtain ⟨hP0, hF0, -, hP1, hF1, -, hP01, hF01, -⟩ :=
    sectionsOf_isInvertible_projective_finite_finrank (𝒱.pullback c ↥A₀) (Limits.pullback.snd c (specMap R ↥A₀)) M.L M.isInvertible
  obtain ⟨hP0', hF0', -, hP1', hF1', -, hP01', hF01', -⟩ :=
    sectionsOf_isInvertible_projective_finite_finrank (𝒱.pullback c ↥A₀) (Limits.pullback.snd c (specMap R ↥A₀)) M'.L M'.isInvertible
  haveI : Module.FinitePresentation ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A0 ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L).M0 :=
    @Module.finitePresentation_of_projective _ _ _ _ _ hP0 hF0
  haveI : Module.FinitePresentation ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A1 ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L).M1 :=
    @Module.finitePresentation_of_projective _ _ _ _ _ hP1 hF1
  haveI : Module.FinitePresentation ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A01 ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L).M01 :=
    @Module.finitePresentation_of_projective _ _ _ _ _ hP01 hF01
  haveI : Module.FinitePresentation ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A0 ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L).M0 :=
    @Module.finitePresentation_of_projective _ _ _ _ _ hP0' hF0'
  haveI : Module.FinitePresentation ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A1 ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L).M1 :=
    @Module.finitePresentation_of_projective _ _ _ _ _ hP1' hF1'
  haveI : Module.FinitePresentation ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A01 ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L).M01 :=
    @Module.finitePresentation_of_projective _ _ _ _ _ hP01' hF01'

  have hval : IsScalarTower.toAlgHom R ↥A₀ A = A₀.val := AlgHom.ext fun _ => rfl
  obtain ⟨β0, β1, β01, hr0, hr1, -, -, -, hs0, hs1, hs01⟩ :=
    exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c ↥A₀ A M.L M.isInvertible.1
  obtain ⟨β0', β1', β01', hr0', hr1', -, -, -, hs0', hs1', hs01'⟩ :=
    exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c ↥A₀ A M'.L M'.isInvertible.1
  let φ0 : ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A0 → ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0 := fun s => show ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0 from
      ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ A))).appLE (𝒱.pullback c ↥A₀).U0 (𝒱.pullback c A).U0 (baseChangeSnd_preimage_U0 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ A))).ge).hom s
  let φ1 : ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A1 → ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1 := fun s => show ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1 from
      ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ A))).appLE (𝒱.pullback c ↥A₀).U1 (𝒱.pullback c A).U1 (baseChangeSnd_preimage_U1 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ A))).ge).hom s
  let φ01 : ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A01 → ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A01 := fun s => show ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A01 from
      ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ A))).appLE ((𝒱.pullback c ↥A₀).U0 ⊓ (𝒱.pullback c ↥A₀).U1) ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) (baseChangeSnd_preimage_inf 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ A))).ge).hom s
  have h' : Nonempty ((M.pullbackAlong (stageHom R (IsScalarTower.toAlgHom R ↥A₀ A))).L ≅
      (M'.pullbackAlong (stageHom R (IsScalarTower.toAlgHom R ↥A₀ A))).L) := by rw [hval]; exact h
  obtain ⟨ψA⟩ := h'
  obtain ⟨ψ0, ψ1, ψ01, hψ0, hψ1, -, -, -⟩ := exists_sectionsOf_linearEquiv_of_iso (𝒱.pullback c A) (Limits.pullback.snd c (specMap R A)) ψA
  obtain ⟨e0, e1, e01, he0, he1, he01, hsq0, hsq1⟩ :=
    ChartBC.exists_intertwines_of_chartIso (k := ↥A₀) (A' := A) (φ0 := φ0) (φ1 := φ1) (φ01 := φ01)
      (S := ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L)) (S' := ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L))
      ⟨β0, β1, β01, hr0, hr1, hs0, hs1, hs01⟩ ⟨β0', β1', β01', hr0', hr1', hs0', hs1', hs01'⟩ ψ0 ψ1 ψ01 hψ0 hψ1
  clear hψ0 hψ1 ψ0 ψ1 ψ01 ψA hr0 hr1 hs0 hs1 hs01 hr0' hr1' hs0' hs1' hs01' β0 β1 β01 β0' β1' β01'

  obtain ⟨D, hD, f0, f1, f01, hf0, hf1, hf01, hfsq0, hfsq1⟩ :=
    exists_fg_descent (k := ↥A₀) (A := A) (S := ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L)) (S' := ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L)) e0 e1 e01 he0 he1 he01 hsq0 hsq1
  clear hsq0 hsq1 he0 he1 he01 e0 e1 e01

  let A₁ : Subalgebra R A := D.restrictScalars R
  have hle : A₀ ≤ A₁ := fun x hx => D.algebraMap_mem (⟨x, hx⟩ : ↥A₀)
  have hA₁ : A₁.FG := fg_restrictScalars_of_fg A₀ hA₀ D hD
  letI instAlg : Algebra ↥A₀ ↥A₁ := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  haveI instIST : IsScalarTower R ↥A₀ ↥A₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htoAlg : IsScalarTower.toAlgHom R ↥A₀ ↥A₁ = Subalgebra.inclusion hle := AlgHom.ext fun _ => rfl

  let j : ↥D →ₐ[↥A₀] ↥A₁ :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
  have hq0 := hf0.push j
  have hq1 := hf1.push j
  have hq01 := hf01.push j
  have hqsq0 := push_square j (f0 : ↥D ⊗[↥A₀] ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L).M0 →ₗ[↥D] ↥D ⊗[↥A₀] ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L).M0)
    (f01 : ↥D ⊗[↥A₀] ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L).M01 →ₗ[↥D] ↥D ⊗[↥A₀] ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L).M01) ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L).r0 ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L).r0 hfsq0
  have hqsq1 := push_square j (f1 : ↥D ⊗[↥A₀] ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L).M1 →ₗ[↥D] ↥D ⊗[↥A₀] ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L).M1)
    (f01 : ↥D ⊗[↥A₀] ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L).M01 →ₗ[↥D] ↥D ⊗[↥A₀] ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L).M01) ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L).r1 ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L).r1 hfsq1

  obtain ⟨γ0, γ1, γ01, gr0, gr1, -, -, -, gs0, gs1, gs01⟩ :=
    exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c ↥A₀ ↥A₁ M.L M.isInvertible.1
  obtain ⟨γ0', γ1', γ01', gr0', gr1', -, -, -, gs0', gs1', gs01'⟩ :=
    exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c ↥A₀ ↥A₁ M'.L M'.isInvertible.1
  obtain ⟨ρ0, ρ1, ρ01, hρ0, hρ1, hρ01⟩ := exists_stage_baseChangeIsos_structureSheaf 𝒱 c ↥A₀ ↥A₁
  let φ0₁ : ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A0 → ((𝒱.pullback c ↥A₁).cover (Limits.pullback.snd c (specMap R ↥A₁))).A0 := fun s => show ((𝒱.pullback c ↥A₁).cover (Limits.pullback.snd c (specMap R ↥A₁))).A0 from
      ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ ↥A₁))).appLE (𝒱.pullback c ↥A₀).U0 (𝒱.pullback c ↥A₁).U0 (baseChangeSnd_preimage_U0 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ ↥A₁))).ge).hom s
  let φ1₁ : ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A1 → ((𝒱.pullback c ↥A₁).cover (Limits.pullback.snd c (specMap R ↥A₁))).A1 := fun s => show ((𝒱.pullback c ↥A₁).cover (Limits.pullback.snd c (specMap R ↥A₁))).A1 from
      ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ ↥A₁))).appLE (𝒱.pullback c ↥A₀).U1 (𝒱.pullback c ↥A₁).U1 (baseChangeSnd_preimage_U1 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ ↥A₁))).ge).hom s
  let φ01₁ : ((𝒱.pullback c ↥A₀).cover (Limits.pullback.snd c (specMap R ↥A₀))).A01 → ((𝒱.pullback c ↥A₁).cover (Limits.pullback.snd c (specMap R ↥A₁))).A01 := fun s => show ((𝒱.pullback c ↥A₁).cover (Limits.pullback.snd c (specMap R ↥A₁))).A01 from
      ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ ↥A₁))).appLE ((𝒱.pullback c ↥A₀).U0 ⊓ (𝒱.pullback c ↥A₀).U1) ((𝒱.pullback c ↥A₁).U0 ⊓ (𝒱.pullback c ↥A₁).U1) (baseChangeSnd_preimage_inf 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥A₀ ↥A₁))).ge).hom s
  obtain ⟨E0, E1, E01, hE0, hE1⟩ :=
    ChartBC.exists_chartIso_of_intertwines (k := ↥A₀) (A' := ↥A₁) (φ0 := φ0₁) (φ1 := φ1₁) (φ01 := φ01₁)
      (S := ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M.L)) (S' := ((𝒱.pullback c ↥A₀).sectionsOf (Limits.pullback.snd c (specMap R ↥A₀)) M'.L))
      ⟨γ0, γ1, γ01, gr0, gr1, gs0, gs1, gs01⟩ ⟨γ0', γ1', γ01', gr0', gr1', gs0', gs1', gs01'⟩
      (mem_span_range_of_algEquiv ρ0 φ0₁ hρ0) (mem_span_range_of_algEquiv ρ1 φ1₁ hρ1)
      (mem_span_range_of_algEquiv ρ01 φ01₁ hρ01)
      (pushEquiv j f0) (pushEquiv j f1) (pushEquiv j f01) hq0 hq1 hq01 hqsq0 hqsq1
  refine ⟨A₁, hA₁, hle, ?_⟩
  rw [← htoAlg]
  exact nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible (𝒱.pullback c ↥A₁) (Limits.pullback.snd c (specMap R ↥A₁)) _ _
    (M.isInvertible.pullback _) (M'.isInvertible.pullback _) E0 E1 E01 hE0 hE1

end AlgebraicGeometry.RelPicard.LFP
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard.LFP"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    AffineLimit.IsLFPInj (relPicardPresheaf c ε) := by
  intro A _ _ A₀ hA₀ x₀ x₀' hx
  induction x₀ using Quotient.inductionOn with
  | h M =>
  induction x₀' using Quotient.inductionOn with
  | h M' =>

  have h : Nonempty ((M.pullbackAlong (RelPicard.LFP.stageHom R A₀.val)).L ≅
      (M'.pullbackAlong (RelPicard.LFP.stageHom R A₀.val)).L) :=
    Quotient.exact (s := RigidifiedLineBundle.setoid (c := c) (ε := ε) _) hx
  obtain ⟨A₁, hA₁, hle, hiso⟩ :=
    RelPicard.LFP.exists_fg_le_nonempty_iso_pullbackAlong R 𝒱 c ε A A₀ hA₀ M M' h
  refine ⟨A₁, hA₁, hle, ?_⟩

  exact Quotient.sound hiso

end S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf (solution)
