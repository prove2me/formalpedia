-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d39f5d70-6b66-512e-8b8c-2801f8f91827

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry TopologicalSpace"
open scoped TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Surjective IsProper Scheme.Hom Scheme.Hom.appLE_comp_appLE isIso_pushoutSection_iff Scheme.Hom.image_preimage_eq_opensRange_inf isPullback_morphismRestrict Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Hom.appTop IsClosedImmersion isAffineOpen_top IsAffineOpen isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage IsAffineHom Scheme.Opens.opensRange_ι Scheme.Hom.appLE Scheme.ΓSpecIso OModulePresheaf.IdealAnnihilates OModulePresheaf.AffHom OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.cechPushforward.chart_le_preimage OModulePresheaf.cechPushforward OModulePresheaf.AffHom.affineChart"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "IdealAnnihilates zero ker Hom AffHom d IsCoherent IsQuasicoherent unit res res_smul res_refl isScalarTower mk module obj res_comp addCommGroup moduleSections cechPushforward.chart_le_preimage cechPushforward AffHom.affineChart"
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

set_option linter.unusedVariables false in

def SecR {R : Type u} [CommRing R] {Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of R)) (V : Y.Opens) : Type u := Γ(Y, V)

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of R))
  (M : Type u) [AddCommGroup M] [Module R M]

namespace SecR

variable {s} (V : Y.Opens)

scoped instance instCommRing : CommRing (SecR s V) := inferInstanceAs (CommRing Γ(Y, V))
scoped instance instAlgebra : Algebra R (SecR s V) := Scheme.TwoAffineOpenCover.algebraOfHom s V

def of : Γ(Y, V) →+* SecR s V := RingHom.id _

def out : SecR s V →+* Γ(Y, V) := RingHom.id _

@[scoped simp] theorem out_of (a : Γ(Y, V)) : out V (of V a : SecR s V) = a := rfl
@[scoped simp] theorem of_out (a : SecR s V) : of V (out V a) = a := rfl

theorem algebraMap_eq (r : R) :
    algebraMap R (SecR s V) r = of V ((s.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl

def resAlg {V V' : Y.Opens} (h : V ≤ V') : SecR s V' →ₐ[R] SecR s V :=
  { toRingHom := (Y.presheaf.map (homOfLE h).op).hom
    commutes' := fun r => by
      change (s.appLE ⊤ V' le_top ≫ Y.presheaf.map (homOfLE h).op).hom _ = (s.appLE ⊤ V le_top).hom _
      rw [Scheme.Hom.appLE_map] }

theorem resAlg_apply {V V' : Y.Opens} (h : V ≤ V') (a : SecR s V') :
    resAlg (s := s) h a = of V ((Y.presheaf.map (homOfLE h).op).hom (out V' a)) := rfl

theorem resAlg_refl (V : Y.Opens) (a : SecR s V) : resAlg (s := s) (le_refl V) a = a := by
  rw [resAlg_apply]
  have : (homOfLE (le_refl V)).op = 𝟙 (Opposite.op V) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this, Y.presheaf.map_id]; rfl

theorem resAlg_resAlg {V₁ V₂ V₃ : Y.Opens} (h₁ : V₁ ≤ V₂) (h₂ : V₂ ≤ V₃) (a : SecR s V₃) :
    resAlg (s := s) h₁ (resAlg h₂ a) = resAlg (h₁.trans h₂) a := by
  simp only [resAlg_apply, out_of]
  rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]; rfl

end SecR
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR"

def tensorDatum : OModulePresheaf s where
  obj V := SecR s V ⊗[R] M
  addCommGroup _ := inferInstance
  module _ := inferInstance
  moduleSections V := show Module (SecR s V) (SecR s V ⊗[R] M) from inferInstance
  isScalarTower V := show IsScalarTower R (SecR s V) (SecR s V ⊗[R] M) from inferInstance
  res h := (SecR.resAlg h).toLinearMap.rTensor M
  res_smul {V V'} h a x := by
    show (SecR.resAlg h).toLinearMap.rTensor M ((SecR.of V' a : SecR s V') • x) =
      (SecR.of V ((Y.presheaf.map (homOfLE h).op).hom a) : SecR s V) • (SecR.resAlg h).toLinearMap.rTensor M x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul b m =>
      rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.smul_tmul',
        smul_eq_mul, smul_eq_mul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_mul]
      rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  res_refl V := by
    refine TensorProduct.ext' fun b m => ?_
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, SecR.resAlg_refl]; rfl
  res_comp h h' := by
    refine TensorProduct.ext' fun b m => ?_
    rw [LinearMap.rTensor_tmul, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, SecR.resAlg_resAlg]

theorem tensorDatum_obj (V : Y.Opens) : (tensorDatum s M).obj V = (SecR s V ⊗[R] M) := rfl

theorem tensorDatum_res_tmul {V V' : Y.Opens} (h : V ≤ V') (b : SecR s V') (m : M) :
    (tensorDatum s M).res h (show (tensorDatum s M).obj V' from b ⊗ₜ m) =
      (show (tensorDatum s M).obj V from SecR.resAlg h b ⊗ₜ m) := rfl

def tensorUnit (V : Y.Opens) : M →ₗ[R] (tensorDatum s M).obj V :=
  (TensorProduct.mk R (SecR s V) M 1 : M →ₗ[R] SecR s V ⊗[R] M)

theorem tensorUnit_apply (V : Y.Opens) (m : M) :
    tensorUnit s M V m = (show (tensorDatum s M).obj V from (1 : SecR s V) ⊗ₜ m) := rfl

theorem res_tensorUnit {V V' : Y.Opens} (h : V ≤ V') (m : M) :
    (tensorDatum s M).res h (tensorUnit s M V' m) = tensorUnit s M V m := by
  rw [tensorUnit_apply, tensorUnit_apply, tensorDatum_res_tmul, map_one]

theorem isCoherent_tensorDatum [Module.Finite R M] : (tensorDatum s M).IsCoherent := fun V =>
  show Module.Finite (SecR s V.1) (SecR s V.1 ⊗[R] M) from inferInstance

section QC

variable {s} {M}

scoped instance algebraBasicOpen (U : Y.Opens) (f : Γ(Y, U)) : Algebra (SecR s U) (SecR s (Y.basicOpen f)) :=
  (SecR.resAlg (s := s) (Y.basicOpen_le f)).toRingHom.toAlgebra

scoped instance isScalarTower_basicOpen (U : Y.Opens) (f : Γ(Y, U)) : IsScalarTower R (SecR s U) (SecR s (Y.basicOpen f)) :=
  IsScalarTower.of_algebraMap_eq fun r => ((SecR.resAlg (s := s) (Y.basicOpen_le f)).commutes r).symm

private theorem _root_.AlgebraicGeometry.OModulePresheaf.isLocalization_basicOpen (U : Y.affineOpens) (f : Γ(Y, U.1)) :
    IsLocalization (Submonoid.powers (SecR.of U.1 f : SecR s U.1)) (SecR s (Y.basicOpen f)) :=
  U.2.isLocalization_basicOpen f

p2m_export "AlgebraicGeometry.OModulePresheaf" "isLocalization_basicOpen"
end QC
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR"

theorem isQuasicoherent_tensorDatum : (tensorDatum s M).IsQuasicoherent := by
  intro U f
  haveI := isLocalization_basicOpen (s := s) U f

  let g : SecR s U.1 →ₗ[SecR s U.1] SecR s (Y.basicOpen f) := Algebra.linearMap _ _
  haveI hg : IsLocalizedModule (Submonoid.powers (SecR.of U.1 f : SecR s U.1)) g := inferInstance
  haveI hG : IsLocalizedModule (Submonoid.powers (SecR.of U.1 f : SecR s U.1))
      (TensorProduct.AlgebraTensorModule.rTensor R M g) := inferInstance

  have hres : ∀ x : SecR s U.1 ⊗[R] M,
      (tensorDatum s M).res (Y.basicOpen_le f) (show (tensorDatum s M).obj U.1 from x) =
        (show (tensorDatum s M).obj (Y.basicOpen f) from TensorProduct.AlgebraTensorModule.rTensor R M g x) :=
    fun x => rfl
  constructor
  · intro x
    obtain ⟨⟨y, ⟨c, n, rfl⟩⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers (SecR.of U.1 f : SecR s U.1))
      (TensorProduct.AlgebraTensorModule.rTensor R M g) x
    refine ⟨n, y, ?_⟩
    rw [hres, ← hy, Submonoid.smul_def]
    show ((SecR.of U.1 f : SecR s U.1) ^ n) • (show SecR s (Y.basicOpen f) ⊗[R] M from x) = _
    rw [← map_pow, ← algebraMap_smul (SecR s (Y.basicOpen f)) ((SecR.of U.1 (f ^ n)) : SecR s U.1)
      (show SecR s (Y.basicOpen f) ⊗[R] M from x)]
    rfl
  · intro y hy
    have h0 : TensorProduct.AlgebraTensorModule.rTensor R M g y = TensorProduct.AlgebraTensorModule.rTensor R M g 0 := by
      rw [map_zero]; exact hy
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (SecR.of U.1 f : SecR s U.1)) h0
    refine ⟨n, ?_⟩
    rw [smul_zero, Submonoid.smul_def] at hc
    show ((SecR.of U.1 f : SecR s U.1) ^ n) • (show SecR s U.1 ⊗[R] M from y) = 0
    rw [← map_pow]
    exact hc

end AlgebraicGeometry.OModulePresheaf
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry"

namespace K73W2A

variable (B C R D : Type u) [CommRing B] [CommRing C] [CommRing R] [CommRing D]
  [Algebra B C] [Algebra B R] [Algebra C D] [Algebra R D] [Algebra B D]
  [IsScalarTower B C D] [IsScalarTower B R D] [Algebra.IsPushout B C R D]
  (L : Type u) [AddCommGroup L] [Module B L] [Module R L] [IsScalarTower B R L]
  (M : Type u) [AddCommGroup M] [Module B M]
  (N : Type u) [AddCommGroup N] [Module C N]
  (pr : L →ₗ[B] M) (β : C ⊗[B] M ≃ₗ[C] N)

def frameEquiv : D ⊗[R] L ≃ₗ[C] C ⊗[B] L := Algebra.IsPushout.cancelBaseChange B C R D L

theorem frameEquiv_one_tmul (x : L) : frameEquiv B C R D L ((1 : D) ⊗ₜ[R] x) = (1 : C) ⊗ₜ[B] x :=
  Algebra.IsPushout.cancelBaseChange_tmul B C R D L x

theorem frameEquiv_symm_tmul (c : C) (x : L) :
    (frameEquiv B C R D L).symm (c ⊗ₜ[B] x) = (algebraMap C D c) ⊗ₜ[R] x :=
  Algebra.IsPushout.cancelBaseChange_symm_tmul B C R D L c x

def theta : D ⊗[R] L →+ N :=
  β.toLinearMap.toAddMonoidHom.comp
    ((pr.baseChange C).toAddMonoidHom.comp (frameEquiv B C R D L).toLinearMap.toAddMonoidHom)

theorem theta_apply (y : D ⊗[R] L) :
    theta B C R D L M N pr β y = β (pr.baseChange C (frameEquiv B C R D L y)) := rfl

theorem algebraMap_smul_eq (c : C) (y : D ⊗[R] L) : (algebraMap C D c) • y = c • y :=
  algebraMap_smul D c y

theorem algebraMap_tmul (r : R) (x : L) : (algebraMap R D r) ⊗ₜ[R] x = (1 : D) ⊗ₜ[R] (r • x) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem theta_one_tmul (x : L) :
    theta B C R D L M N pr β ((1 : D) ⊗ₜ[R] x) = β ((1 : C) ⊗ₜ[B] pr x) := by
  rw [theta_apply, frameEquiv_one_tmul, LinearMap.baseChange_tmul]

theorem theta_smul (c : C) (y : D ⊗[R] L) :
    theta B C R D L M N pr β ((algebraMap C D c) • y) = c • theta B C R D L M N pr β y := by
  rw [theta_apply, theta_apply, algebraMap_smul_eq, LinearEquiv.map_smul, LinearMap.map_smul,
    LinearEquiv.map_smul]

theorem theta_tmul (c : C) (r : R) (x : L) :
    theta B C R D L M N pr β ((algebraMap C D c * algebraMap R D r) ⊗ₜ[R] x) =
      c • β ((1 : C) ⊗ₜ[B] pr (r • x)) := by
  rw [← smul_eq_mul, ← TensorProduct.smul_tmul', theta_smul, algebraMap_tmul, theta_one_tmul]

omit [Module B L] [IsScalarTower B R L] in
include B in

private theorem _root_.K73W2A.induction_on {P : D ⊗[R] L → Prop} (h0 : P 0)
    (htmul : ∀ (c : C) (r : R) (x : L), P ((algebraMap C D c * algebraMap R D r) ⊗ₜ[R] x))
    (hadd : ∀ y z, P y → P z → P (y + z)) (y : D ⊗[R] L) : P y := by
  induction y using TensorProduct.induction_on with
  | zero => exact h0
  | tmul d x =>
    have hbc : IsBaseChange C (IsScalarTower.toAlgHom B R D).toLinearMap :=
      Algebra.IsPushout.out (R := B) (S := C) (R' := R) (S' := D)
    obtain ⟨w, rfl⟩ := hbc.equiv.surjective d
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, TensorProduct.zero_tmul]; exact h0
    | tmul c r =>
      rw [IsBaseChange.equiv_tmul, AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply,
        Algebra.smul_def]
      exact htmul c r x
    | add w₁ w₂ h₁ h₂ => rw [map_add, TensorProduct.add_tmul]; exact hadd _ _ h₁ h₂
  | add y z hy hz => exact hadd y z hy hz

p2m_export "K73W2A" "induction_on"
theorem baseChange_apply_eq_lTensor (z : C ⊗[B] L) : pr.baseChange C z = pr.lTensor C z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c x => rw [LinearMap.baseChange_tmul, LinearMap.lTensor_tmul]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

theorem theta_surjective (hpr : Function.Surjective pr) :
    Function.Surjective (theta B C R D L M N pr β) := by
  intro n
  obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective C hpr (β.symm n)
  refine ⟨(frameEquiv B C R D L).symm w, ?_⟩
  rw [theta_apply, LinearEquiv.apply_symm_apply, baseChange_apply_eq_lTensor, hw,
    LinearEquiv.apply_symm_apply]

include β in

theorem algebraMap_smul_eq_zero (hpr : Function.Surjective pr) (K : Ideal B)
    (hker : LinearMap.ker pr = K • (⊤ : Submodule B L)) {k : B} (hk : k ∈ K) (n : N) :
    (algebraMap B C k) • n = 0 := by
  obtain ⟨z, rfl⟩ := β.surjective n
  rw [← LinearEquiv.map_smul]
  convert β.map_zero
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero]
  | tmul c m =>
    obtain ⟨x, rfl⟩ := hpr m
    rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul, ← LinearMap.map_smul]
    have : k • x ∈ LinearMap.ker pr := by
      rw [hker]; exact Submodule.smul_mem_smul hk Submodule.mem_top
    rw [LinearMap.mem_ker] at this
    rw [this, TensorProduct.tmul_zero]
  | add z₁ z₂ h₁ h₂ => rw [smul_add, h₁, h₂, add_zero]

theorem tmul_mem_smul_top (K : Ideal B) (d : D) {p : L} (hp : p ∈ K • (⊤ : Submodule B L)) :
    d ⊗ₜ[R] p ∈ K • (⊤ : Submodule B (D ⊗[R] L)) := by
  induction hp using Submodule.smul_induction_on' with
  | smul k hk l _ =>
    rw [← algebraMap_smul R k l, TensorProduct.tmul_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul hk Submodule.mem_top
  | add p₁ p₂ _ _ h₁ h₂ => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h₁ h₂

theorem theta_eq_zero_iff (hpr : Function.Surjective pr) (K : Ideal B)
    (hker : LinearMap.ker pr = K • (⊤ : Submodule B L)) (y : D ⊗[R] L) :
    theta B C R D L M N pr β y = 0 ↔
      y ∈ K.map (algebraMap B R) • (⊤ : Submodule R (D ⊗[R] L)) := by
  rw [← Submodule.restrictScalars_mem B, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  constructor
  · intro h
    rw [theta_apply, LinearEquiv.map_eq_zero_iff, baseChange_apply_eq_lTensor] at h
    have hex : Function.Exact (pr.ker.subtype.lTensor C) (pr.lTensor C) :=
      lTensor_exact C (LinearMap.exact_subtype_ker_map pr) hpr
    obtain ⟨w, hw⟩ := (hex _).mp h
    rw [← (frameEquiv B C R D L).symm_apply_apply y, ← hw]
    clear h hw
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | tmul c p =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, frameEquiv_symm_tmul]
      exact tmul_mem_smul_top B R D L K _ (hker ▸ p.2)
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add]; exact Submodule.add_mem _ h₁ h₂
  · intro h
    induction h using Submodule.smul_induction_on' with
    | smul k hk y _ =>
      rw [← algebraMap_smul D k y, IsScalarTower.algebraMap_apply B C D k, theta_smul]
      exact algebraMap_smul_eq_zero B C L M N pr β hpr K hker hk _
    | add y₁ y₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]

theorem theta_naturality
    (C₁ D₁ : Type u) [CommRing C₁] [CommRing D₁] [Algebra B C₁] [Algebra C₁ D₁] [Algebra R D₁]
    [Algebra B D₁] [IsScalarTower B C₁ D₁] [IsScalarTower B R D₁] [Algebra.IsPushout B C₁ R D₁]
    (N₁ : Type u) [AddCommGroup N₁] [Module C₁ N₁] (β₁ : C₁ ⊗[B] M ≃ₗ[C₁] N₁)
    (ρC : C →ₐ[B] C₁) (ρD : D →ₐ[R] D₁)
    (hρ : ∀ c : C, ρD (algebraMap C D c) = algebraMap C₁ D₁ (ρC c))
    (ρN : N →+ N₁) (hρN_smul : ∀ (c : C) (z : N), ρN (c • z) = ρC c • ρN z)
    (hρN_β : ∀ m : M, ρN (β ((1 : C) ⊗ₜ[B] m)) = β₁ ((1 : C₁) ⊗ₜ[B] m)) (y : D ⊗[R] L) :
    ρN (theta B C R D L M N pr β y) =
      theta B C₁ R D₁ L M N₁ pr β₁ (ρD.toLinearMap.rTensor L y) := by
  induction y using induction_on B C R D L with
  | h0 => simp only [map_zero]
  | htmul c r x =>
    rw [theta_tmul, hρN_smul, hρN_β, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_mul, hρ,
      AlgHom.commutes, theta_tmul]
  | hadd y z hy hz => simp only [map_add, hy, hz]

theorem theta_level
    (M₀ : Type u) [AddCommGroup M₀] [Module B M₀] (N₀ : Type u) [AddCommGroup N₀] [Module C N₀]
    (pr₀ : L →ₗ[B] M₀) (β₀ : C ⊗[B] M₀ ≃ₗ[C] N₀)
    (φM : M →ₗ[B] M₀) (hφM : ∀ x : L, φM (pr x) = pr₀ x)
    (φN : N →+ N₀) (hφN_smul : ∀ (c : C) (z : N), φN (c • z) = c • φN z)
    (hφN_β : ∀ m : M, φN (β ((1 : C) ⊗ₜ[B] m)) = β₀ ((1 : C) ⊗ₜ[B] φM m)) (y : D ⊗[R] L) :
    φN (theta B C R D L M N pr β y) = theta B C R D L M₀ N₀ pr₀ β₀ y := by
  induction y using induction_on B C R D L with
  | h0 => simp only [map_zero]
  | htmul c r x => rw [theta_tmul, hφN_smul, hφN_β, hφM, theta_tmul]
  | hadd y z hy hz => simp only [map_add, hy, hz]

end K73W2A
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Surjective IsProper Scheme.Hom Scheme.Hom.appLE_comp_appLE isIso_pushoutSection_iff Scheme.Hom.image_preimage_eq_opensRange_inf isPullback_morphismRestrict Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Hom.appTop IsClosedImmersion isAffineOpen_top IsAffineOpen isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage IsAffineHom Scheme.Opens.opensRange_ι Scheme.Hom.appLE Scheme.ΓSpecIso OModulePresheaf.IdealAnnihilates OModulePresheaf.AffHom OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.cechPushforward.chart_le_preimage OModulePresheaf.cechPushforward OModulePresheaf.AffHom.affineChart"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "IdealAnnihilates zero ker Hom AffHom d IsCoherent IsQuasicoherent unit res res_smul res_refl isScalarTower mk module obj res_comp addCommGroup moduleSections cechPushforward.chart_le_preimage cechPushforward AffHom.affineChart"
namespace W2
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

open CategoryTheory.Limits

variable {V' P : Scheme.{u}} (p : V' ⟶ P) (W : P.affineOpens) (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]

abbrev pW : V'.Opens := p ⁻¹ᵁ W.1

def qW : ((pW p W) : Scheme.{u}) ⟶ Spec Γ(P, W.1) := (p ∣_ W.1) ≫ W.2.isoSpec.hom

abbrev bR : Spec (CommRingCat.of R) ⟶ Spec Γ(P, W.1) := Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R))

abbrev Y : Scheme.{u} := pullback (qW p W) (bR W R)

abbrev sY : Y p W R ⟶ Spec (CommRingCat.of R) := pullback.snd (qW p W) (bR W R)

abbrev fY : Y p W R ⟶ (pW p W : Scheme.{u}) := pullback.fst (qW p W) (bR W R)

abbrev tY : Y p W R ⟶ V' := fY p W R ≫ (pW p W).ι

scoped instance isAffineHom_fY : IsAffineHom (fY p W R) := MorphismProperty.pullback_fst _ _ inferInstance

theorem isPullback_tY_sY : IsPullback (tY p W R) (sY p W R) p (bR W R ≫ W.2.fromSpec) := by
  have h0 := (isPullback_morphismRestrict p W.1).flip
  have h1 : IsPullback (pW p W).ι (qW p W) p (W.2.isoSpec.inv ≫ W.1.ι) :=
    IsPullback.of_iso h0 (Iso.refl _) (Iso.refl _) W.2.isoSpec (Iso.refl _) (by simp) (by simp [qW]) (by simp)
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
  have h2 : IsPullback (fY p W R) (sY p W R) (qW p W) (bR W R) := IsPullback.of_hasPullback _ _
  rw [← W.2.isoSpec_inv_ι]
  exact h2.paste_horiz h1

scoped instance isProper_qW [IsProper p] : IsProper (qW p W) := by unfold qW; infer_instance

scoped instance isProper_sY [IsProper p] : IsProper (sY p W R) := MorphismProperty.pullback_snd _ _ inferInstance

theorem isAffineOpen_ι_preimage (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ W.1) : IsAffineOpen ((pW p W).ι ⁻¹ᵁ V.1) := by
  rw [← (pW p W).ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.2 h]
  exact V.2

theorem tY_preimage (V : V'.Opens) : tY p W R ⁻¹ᵁ V = fY p W R ⁻¹ᵁ ((pW p W).ι ⁻¹ᵁ V) := rfl

theorem isAffineOpen_tY_preimage (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ W.1) : IsAffineOpen (tY p W R ⁻¹ᵁ V.1) := by
  rw [tY_preimage]
  exact (isAffineOpen_ι_preimage p W V h).preimage _

section Pushout

variable (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ W.1)

theorem top_le_preimage : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (bR W R ≫ W.2.fromSpec) ⁻¹ᵁ W.1 := by
  rw [Scheme.Hom.comp_preimage, W.2.fromSpec_preimage_self]
  exact le_rfl

abbrev iBC : Γ(P, W.1) ⟶ Γ(V', V.1) := p.appLE W.1 V.1 h
abbrev iBR' : Γ(P, W.1) ⟶ Γ(Spec (CommRingCat.of R), ⊤) := (bR W R ≫ W.2.fromSpec).appLE W.1 ⊤ (top_le_preimage W R)
abbrev iCD : Γ(V', V.1) ⟶ Γ(Y p W R, tY p W R ⁻¹ᵁ V.1) := (tY p W R).appLE V.1 (tY p W R ⁻¹ᵁ V.1) le_rfl
abbrev iR'D : Γ(Spec (CommRingCat.of R), ⊤) ⟶ Γ(Y p W R, tY p W R ⁻¹ᵁ V.1) := (sY p W R).appLE ⊤ (tY p W R ⁻¹ᵁ V.1) le_top

theorem isPushout_sections :
    IsPushout (iBC p W V h) (iBR' W R) (iCD p W R V) (iR'D p W R V) := by
  have H := isPullback_tY_sY p W R
  have hUST := top_le_preimage W R
  have hUY : tY p W R ⁻¹ᵁ V.1 = tY p W R ⁻¹ᵁ V.1 ⊓ sY p W R ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isAffineOpen H hUST h hUY W.2 (isAffineOpen_top _) V.2
  exact (isIso_pushoutSection_iff H hUST h hUY).1 hiso

end Pushout
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf"

end AlgebraicGeometry.OModulePresheaf.W2
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.W2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Surjective IsProper Scheme.Hom Scheme.Hom.appLE_comp_appLE isIso_pushoutSection_iff Scheme.Hom.image_preimage_eq_opensRange_inf isPullback_morphismRestrict Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Hom.appTop IsClosedImmersion isAffineOpen_top IsAffineOpen isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage IsAffineHom Scheme.Opens.opensRange_ι Scheme.Hom.appLE Scheme.ΓSpecIso OModulePresheaf.IdealAnnihilates OModulePresheaf.AffHom OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.cechPushforward.chart_le_preimage OModulePresheaf.cechPushforward OModulePresheaf.AffHom.affineChart"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "IdealAnnihilates zero ker Hom AffHom d IsCoherent IsQuasicoherent unit res res_smul res_refl isScalarTower mk module obj res_comp addCommGroup moduleSections cechPushforward.chart_le_preimage cechPushforward AffHom.affineChart"
namespace W2
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

open CategoryTheory.Limits

variable {V' P : Scheme.{u}} (p : V' ⟶ P) (W : P.affineOpens) (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]

theorem iBR'_ΓSpecIso :
    iBR' W R ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom (algebraMap Γ(P, W.1) R) := by
  have h₁ : (⊤ : (Spec Γ(P, W.1)).Opens) ≤ W.2.fromSpec ⁻¹ᵁ W.1 := by rw [W.2.fromSpec_preimage_self]
  have e1 : iBR' W R = W.2.fromSpec.appLE W.1 ⊤ h₁ ≫ (bR W R).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
  have e2 : W.2.fromSpec.appLE W.1 ⊤ h₁ = (Scheme.ΓSpecIso Γ(P, W.1)).inv := by
    rw [Scheme.Hom.appLE, W.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    have : ((eqToHom W.2.fromSpec_preimage_self).op ≫ (homOfLE h₁).op :
        (Opposite.op ⊤ : (Spec Γ(P, W.1)).Opensᵒᵖ) ⟶ Opposite.op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.comp_id]
  have e3 : (bR W R).appLE ⊤ ⊤ le_top = (bR W R).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [e1, e2, e3, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section AlgPushout

variable (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ W.1)

abbrev D : Type u := SecR (sY p W R) (tY p W R ⁻¹ᵁ V.1)

abbrev algBC : Algebra Γ(P, W.1) Γ(V', V.1) := (p.appLE W.1 V.1 h).hom.toAlgebra

abbrev algCD : Algebra Γ(V', V.1) (D p W R V) := ((tY p W R).app V.1).hom.toAlgebra

abbrev algBD : Algebra Γ(P, W.1) (D p W R V) := (((tY p W R).app V.1).hom.comp (p.appLE W.1 V.1 h).hom).toAlgebra

theorem isScalarTower_BCD :
    letI := algBC p W V h; letI := algCD p W R V; letI := algBD p W R V h
    IsScalarTower Γ(P, W.1) Γ(V', V.1) (D p W R V) :=
  letI := algBC p W V h; letI := algCD p W R V; letI := algBD p W R V h
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem iCD_eq : iCD p W R V = (tY p W R).app V.1 := (Scheme.Hom.app_eq_appLE _).symm

theorem algebraMap_R_D : CommRingCat.ofHom (algebraMap R (D p W R V)) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ iR'D p W R V := rfl

theorem isScalarTower_BRD :
    letI := algBD p W R V h
    IsScalarTower Γ(P, W.1) R (D p W R V) := by
  letI := algBD p W R V h
  refine IsScalarTower.of_algebraMap_eq fun b => ?_
  have hsq := congrArg (fun φ => CommRingCat.Hom.hom φ b) (isPushout_sections p W R V h).w
  have k1 : algebraMap Γ(P, W.1) R b = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((iBR' W R).hom b) := by
    have := congrArg (fun φ => CommRingCat.Hom.hom φ b) (iBR'_ΓSpecIso W R)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this.symm
  have k3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
    fun x => by
      have := congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
      simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] at this
      exact this
  show ((tY p W R).app V.1).hom ((p.appLE W.1 V.1 h).hom b) =
    (iR'D p W R V).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (algebraMap Γ(P, W.1) R b))
  rw [k1, k3, ← iCD_eq]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hsq
  exact hsq

theorem algebra_isPushout :
    letI := algBC p W V h; letI := algCD p W R V; letI := algBD p W R V h
    haveI := isScalarTower_BCD p W R V h; haveI := isScalarTower_BRD p W R V h
    Algebra.IsPushout Γ(P, W.1) Γ(V', V.1) R (D p W R V) := by
  letI := algBC p W V h; letI := algCD p W R V; letI := algBD p W R V h
  haveI := isScalarTower_BCD p W R V h; haveI := isScalarTower_BRD p W R V h
  refine CommRingCat.isPushout_iff_isPushout.1 ?_
  refine IsPushout.of_iso (isPushout_sections p W R V h) (Iso.refl _) (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of R)) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl
  · rw [Iso.refl_hom, Category.id_comp, iBR'_ΓSpecIso]
  · simp only [Iso.refl_hom, Category.id_comp, iCD_eq]; rfl
  · rw [algebraMap_R_D]
    ext x
    change (iR'D p W R V).hom x =
      (iR'D p W R V).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x))
    have := congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
    simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] at this
    rw [this]

end AlgPushout
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.W2"

end AlgebraicGeometry.OModulePresheaf.W2
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.W2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.W2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.W2"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.SecR P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf.W2"

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry TopologicalSpace"
open scoped TensorProduct

p2m_open "AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.AlgebraicGeometry.OModulePresheaf"

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (L : Type u) [AddCommGroup L] [Module Γ(P, W.1) L] [Module R L] [IsScalarTower Γ(P, W.1) R L]
    [Module.Finite R L]
    (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1)
    (hprc : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L)) :
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (CommRingCat.of R)) (_ : IsProper sY) (t : Y ⟶ V'),
      IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec) ∧
      (∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1)) ∧
      ∃ (G : OModulePresheaf sY) (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
        (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1)),
        G.IsCoherent ∧ G.IsQuasicoherent ∧
        (∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x) ∧
        (∀ U : Y.affineOpens,
          letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
          ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
          (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y) ∧
        (∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
          (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
          (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
          (φ' n).app V (θ (n + 1) V h y) = θ n V h y) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
          θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
          θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule R (G.obj (t ⁻¹ᵁ V.1)))) := by
  classical
  haveI : IsProper (g ≫ i) := inferInstance

  let Bq : Γ(Spec (CommRingCat.of A), ⊤) ⟶ Γ(P, W.1) := q.appLE ⊤ W.1 le_top
  let J : Ideal Γ(P, W.1) := I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom
  let θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 →
      ((tensorDatum (W2.sY (g ≫ i) W R) L).obj (W2.tY (g ≫ i) W R ⁻¹ᵁ V.1) →+ (F' n).obj V.1) :=
    fun n V hV =>
      letI := W2.algBC (g ≫ i) W V hV; letI := W2.algCD (g ≫ i) W R V; letI := W2.algBD (g ≫ i) W R V hV
      haveI := W2.isScalarTower_BCD (g ≫ i) W R V hV; haveI := W2.isScalarTower_BRD (g ≫ i) W R V hV
      haveI := W2.algebra_isPushout (g ≫ i) W R V hV
      K73W2A.theta Γ(P, W.1) Γ(V', V.1) R (W2.D (g ≫ i) W R V) L ((F n).obj W.1) ((F' n).obj V.1) (pr n)
        (hβ n W V hV).choose
  refine ⟨W2.Y (g ≫ i) W R, W2.sY (g ≫ i) W R, inferInstance, W2.tY (g ≫ i) W R, W2.isPullback_tY_sY (g ≫ i) W R,
    fun V hV => W2.isAffineOpen_tY_preimage (g ≫ i) W R V hV,
    tensorDatum (W2.sY (g ≫ i) W R) L, fun U => tensorUnit (W2.sY (g ≫ i) W R) L U, θ,
    isCoherent_tensorDatum _ L, isQuasicoherent_tensorDatum _ L,
    fun U U' hUU' x => res_tensorUnit _ L hUU' x,
    fun U => ⟨LinearEquiv.refl _ _, fun x => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro n V hV c y
    letI := W2.algBC (g ≫ i) W V hV; letI := W2.algCD (g ≫ i) W R V; letI := W2.algBD (g ≫ i) W R V hV
    haveI := W2.isScalarTower_BCD (g ≫ i) W R V hV; haveI := W2.isScalarTower_BRD (g ≫ i) W R V hV
    haveI := W2.algebra_isPushout (g ≫ i) W R V hV
    exact K73W2A.theta_smul Γ(P, W.1) Γ(V', V.1) R (W2.D (g ≫ i) W R V) L ((F n).obj W.1) ((F' n).obj V.1) (pr n)
      (hβ n W V hV).choose c y
  ·
    intro n V₁ V₂ h₁ h₂ hV y
    letI iBC₂ := W2.algBC (g ≫ i) W V₂ h₂; letI iCD₂ := W2.algCD (g ≫ i) W R V₂; letI iBD₂ := W2.algBD (g ≫ i) W R V₂ h₂
    haveI := W2.isScalarTower_BCD (g ≫ i) W R V₂ h₂; haveI := W2.isScalarTower_BRD (g ≫ i) W R V₂ h₂
    haveI := W2.algebra_isPushout (g ≫ i) W R V₂ h₂
    letI iBC₁ := W2.algBC (g ≫ i) W V₁ h₁; letI iCD₁ := W2.algCD (g ≫ i) W R V₁; letI iBD₁ := W2.algBD (g ≫ i) W R V₁ h₁
    haveI := W2.isScalarTower_BCD (g ≫ i) W R V₁ h₁; haveI := W2.isScalarTower_BRD (g ≫ i) W R V₁ h₁
    haveI := W2.algebra_isPushout (g ≫ i) W R V₁ h₁
    have htV : W2.tY (g ≫ i) W R ⁻¹ᵁ V₁.1 ≤ W2.tY (g ≫ i) W R ⁻¹ᵁ V₂.1 := (Opens.map (W2.tY (g ≫ i) W R).base).monotone hV

    let ρC : Γ(V', V₂.1) →ₐ[Γ(P, W.1)] Γ(V', V₁.1) :=
      { toRingHom := (V'.presheaf.map (homOfLE hV).op).hom
        commutes' := fun b => by
          change ((g ≫ i).appLE W.1 V₂.1 h₂ ≫ V'.presheaf.map (homOfLE hV).op).hom b = ((g ≫ i).appLE W.1 V₁.1 h₁).hom b
          rw [Scheme.Hom.appLE_map] }
    have hρ : ∀ c : Γ(V', V₂.1), SecR.resAlg (s := W2.sY (g ≫ i) W R) htV (algebraMap Γ(V', V₂.1) (W2.D (g ≫ i) W R V₂) c) =
        algebraMap Γ(V', V₁.1) (W2.D (g ≫ i) W R V₁) (ρC c) := fun c => by
      change ((W2.tY (g ≫ i) W R).app V₂.1 ≫ (W2.Y (g ≫ i) W R).presheaf.map (homOfLE htV).op).hom c =
        (V'.presheaf.map (homOfLE hV).op ≫ (W2.tY (g ≫ i) W R).app V₁.1).hom c
      rw [← W2.iCD_eq, ← W2.iCD_eq, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    have key := K73W2A.theta_naturality Γ(P, W.1) Γ(V', V₂.1) R (W2.D (g ≫ i) W R V₂) L ((F n).obj W.1)
      ((F' n).obj V₂.1) (pr n) (hβ n W V₂ h₂).choose Γ(V', V₁.1) (W2.D (g ≫ i) W R V₁) ((F' n).obj V₁.1)
      (hβ n W V₁ h₁).choose ρC (SecR.resAlg (s := W2.sY (g ≫ i) W R) htV) hρ ((F' n).res hV).toAddMonoidHom
      (fun c z => (F' n).res_smul hV c z)
      (fun m => by
        show (F' n).res hV ((hβ n W V₂ h₂).choose ((1 : Γ(V', V₂.1)) ⊗ₜ m)) = (hβ n W V₁ h₁).choose ((1 : Γ(V', V₁.1)) ⊗ₜ m)
        rw [(hβ n W V₂ h₂).choose_spec, (hβ n W V₁ h₁).choose_spec]
        exact hηV n W V₁ V₂ h₁ h₂ hV m) y
    exact key
  ·
    intro n V hV y
    letI := W2.algBC (g ≫ i) W V hV; letI := W2.algCD (g ≫ i) W R V; letI := W2.algBD (g ≫ i) W R V hV
    haveI := W2.isScalarTower_BCD (g ≫ i) W R V hV; haveI := W2.isScalarTower_BRD (g ≫ i) W R V hV
    haveI := W2.algebra_isPushout (g ≫ i) W R V hV
    exact K73W2A.theta_level Γ(P, W.1) Γ(V', V.1) R (W2.D (g ≫ i) W R V) L ((F (n + 1)).obj W.1)
      ((F' (n + 1)).obj V.1) (pr (n + 1)) (hβ (n + 1) W V hV).choose ((F n).obj W.1) ((F' n).obj V.1) (pr n)
      (hβ n W V hV).choose ((φ n).appSections W) (fun x => hprc n x) ((φ' n).app V).toAddMonoidHom
      (fun c z => (φ' n).app_smul V c z)
      (fun m => by
        show (φ' n).app V ((hβ (n + 1) W V hV).choose ((1 : Γ(V', V.1)) ⊗ₜ m)) =
          (hβ n W V hV).choose ((1 : Γ(V', V.1)) ⊗ₜ (φ n).app W m)
        rw [(hβ (n + 1) W V hV).choose_spec, (hβ n W V hV).choose_spec]
        exact hηφ n W V hV m) y
  ·
    intro n V hV x
    letI := W2.algBC (g ≫ i) W V hV; letI := W2.algCD (g ≫ i) W R V; letI := W2.algBD (g ≫ i) W R V hV
    haveI := W2.isScalarTower_BCD (g ≫ i) W R V hV; haveI := W2.isScalarTower_BRD (g ≫ i) W R V hV
    haveI := W2.algebra_isPushout (g ≫ i) W R V hV
    rw [tensorUnit_apply]
    exact (K73W2A.theta_one_tmul Γ(P, W.1) Γ(V', V.1) R (W2.D (g ≫ i) W R V) L ((F n).obj W.1) ((F' n).obj V.1)
      (pr n) (hβ n W V hV).choose x).trans ((hβ n W V hV).choose_spec (pr n x))
  ·
    intro n V hV
    letI := W2.algBC (g ≫ i) W V hV; letI := W2.algCD (g ≫ i) W R V; letI := W2.algBD (g ≫ i) W R V hV
    haveI := W2.isScalarTower_BCD (g ≫ i) W R V hV; haveI := W2.isScalarTower_BRD (g ≫ i) W R V hV
    haveI := W2.algebra_isPushout (g ≫ i) W R V hV
    exact K73W2A.theta_surjective Γ(P, W.1) Γ(V', V.1) R (W2.D (g ≫ i) W R V) L ((F n).obj W.1) ((F' n).obj V.1)
      (pr n) (hβ n W V hV).choose (hprs n)
  ·
    intro n V hV y
    letI := W2.algBC (g ≫ i) W V hV; letI := W2.algCD (g ≫ i) W R V; letI := W2.algBD (g ≫ i) W R V hV
    haveI := W2.isScalarTower_BCD (g ≫ i) W R V hV; haveI := W2.isScalarTower_BRD (g ≫ i) W R V hV
    haveI := W2.algebra_isPushout (g ≫ i) W R V hV
    have hk := K73W2A.theta_eq_zero_iff Γ(P, W.1) Γ(V', V.1) R (W2.D (g ≫ i) W R V) L ((F n).obj W.1)
      ((F' n).obj V.1) (pr n) (hβ n W V hV).choose (hprs n) (J ^ (n + 1)) (hprk n) y
    rw [Ideal.map_pow, Ideal.map_map] at hk
    exact hk

end S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top (solution)
