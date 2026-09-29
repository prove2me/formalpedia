-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3dfd158e-e82e-5ac4-8132-f1a78074eacd

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry TensorProduct"

noncomputable section

namespace P2mPicCompareSol

variable {X : Scheme.{u}}

section BasicOpen

variable (N : X.Modules) (U : X.Opens) (f : Γ(X, U))

@[reducible] def modBO : Module Γ(X, U) Γ(N, X.basicOpen f) :=
  Module.compHom Γ(N, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))

attribute [local instance] modBO

scoped instance isScalarTower_modBO : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(N, X.basicOpen f) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def resBO : Γ(N, U) →ₗ[Γ(X, U)] Γ(N, X.basicOpen f) where
  toFun := N.presheaf.map (homOfLE (X.basicOpen_le f)).op
  map_add' x y := map_add _ x y
  map_smul' a x := Scheme.Modules.map_smul N (homOfLE (X.basicOpen_le f)) a x

theorem resBO_apply (x : Γ(N, U)) : resBO N U f x = N.presheaf.map (homOfLE (X.basicOpen_le f)).op x := rfl

def toSpecTop (X : Scheme.{u}) : X ⟶ Spec (.of Γ(X, ⊤)) := X.toSpecΓ

theorem isLocalizedModule_resBO (hN : Scheme.Modules.IsInvertible N) (hU : IsAffineOpen U) :
    IsLocalizedModule (Submonoid.powers f) (resBO N U f) := by
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  obtain ⟨h1, h2⟩ :=
    (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial (toSpecTop X) N hN.1) ⟨U, hU⟩ f
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow n
    have := hu.smul_bijective (β := Γ(N, X.basicOpen f))
    convert this using 1
    funext a
    rw [Module.algebraMap_end_apply, algebraMap_smul]
  · intro y
    obtain ⟨n, x, hx⟩ := h1 y
    exact ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, hx.symm⟩
  · intro x₁ x₂ h
    have h0 : N.presheaf.map (homOfLE (X.basicOpen_le f)).op (x₁ - x₂) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h
    obtain ⟨n, hn⟩ := h2 (x₁ - x₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]
    exact hn

end BasicOpen

attribute [local instance] modBO

section Theta

variable (L M : X.Modules)

abbrev theta (U : X.Opens) : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U) :=
  TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U)

theorem theta_tmul (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)) :
    theta L M U (s ⊗ₜ t) = Scheme.Modules.tensorSections s t := by
  simp [theta]

variable (U : X.Opens) (f : Γ(X, U))

def thetaBO : Γ(L, X.basicOpen f) ⊗[Γ(X, U)] Γ(M, X.basicOpen f) →ₗ[Γ(X, U)] Γ(L ⊗ M, X.basicOpen f) :=
  TensorProduct.lift
    (LinearMap.mk₂ Γ(X, U) (fun x y => Scheme.Modules.tensorSections x y)
      (fun x₁ x₂ y => Scheme.Modules.tensorSections_add_left x₁ x₂ y)
      (fun a x y => by
        try dsimp only
        rw [← algebraMap_smul Γ(X, X.basicOpen f) a x, Scheme.Modules.tensorSections_smul_left,
          algebraMap_smul])
      (fun x y₁ y₂ => Scheme.Modules.tensorSections_add_right x y₁ y₂)
      (fun a x y => by
        try dsimp only
        rw [← algebraMap_smul Γ(X, X.basicOpen f) a y, Scheme.Modules.tensorSections_smul_right,
          algebraMap_smul]))

theorem thetaBO_tmul (x : Γ(L, X.basicOpen f)) (y : Γ(M, X.basicOpen f)) :
    thetaBO L M U f (x ⊗ₜ y) = Scheme.Modules.tensorSections x y := rfl

theorem thetaBO_comp_map :
    thetaBO L M U f ∘ₗ TensorProduct.map (resBO L U f) (resBO M U f) = resBO (L ⊗ M) U f ∘ₗ theta L M U := by
  refine TensorProduct.ext' fun s t => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul, thetaBO_tmul, theta_tmul,
    resBO_apply, resBO_apply, resBO_apply]
  exact (Scheme.Modules.map_homOfLE_tensorSections (X.basicOpen_le f) s t).symm

theorem thetaBO_bijective_of (hU : IsAffineOpen U)
    (h : Function.Bijective (theta L M (X.basicOpen f))) : Function.Bijective (thetaBO L M U f) := by
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  let e : Γ(L, X.basicOpen f) ⊗[Γ(X, X.basicOpen f)] Γ(M, X.basicOpen f) ≃ₗ[Γ(X, U)]
      Γ(L, X.basicOpen f) ⊗[Γ(X, U)] Γ(M, X.basicOpen f) :=
    (IsLocalization.moduleTensorEquiv (Submonoid.powers f) Γ(X, X.basicOpen f)
      Γ(L, X.basicOpen f) Γ(M, X.basicOpen f)).restrictScalars Γ(X, U)
  have he : ∀ x y, e (x ⊗ₜ[Γ(X, X.basicOpen f)] y) = x ⊗ₜ[Γ(X, U)] y := fun x y => rfl

  have hcomp : ∀ z, thetaBO L M U f (e z) = theta L M (X.basicOpen f) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul x y => rw [he, thetaBO_tmul, theta_tmul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hfun : (thetaBO L M U f : _ → _) = theta L M (X.basicOpen f) ∘ e.symm := by
    funext z
    rw [Function.comp_apply, ← hcomp, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact h.comp e.symm.bijective

end Theta

section Frames

variable {L M : X.Modules} {D : X.Opens}

theorem res_self (N : X.Modules) (s : Γ(N, D)) : N.presheaf.map (homOfLE (le_refl D)).op s = s := by
  have : (homOfLE (le_refl D)).op = 𝟙 (Opposite.op D) := Subsingleton.elim _ _
  rw [this, N.presheaf.map_id]
  rfl

theorem bijective_smul_of_isFrameOn {N : X.Modules} {s : Γ(N, D)} (hs : Scheme.Modules.IsFrameOn s D) :
    Function.Bijective fun g : Γ(X, D) => g • s := by
  have h := hs.bijective (le_refl D) (le_refl D)
  rwa [res_self] at h

theorem theta_bijective_of_isFrameOn {s : Γ(L, D)} {t : Γ(M, D)}
    (hs : Scheme.Modules.IsFrameOn s D) (ht : Scheme.Modules.IsFrameOn t D) :
    Function.Bijective (theta L M D) := by
  have hst := bijective_smul_of_isFrameOn (hs.tensorSections ht)
  let σ : Γ(X, D) ≃ₗ[Γ(X, D)] Γ(L, D) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, D) Γ(L, D) s) (bijective_smul_of_isFrameOn hs)
  let τ : Γ(X, D) ≃ₗ[Γ(X, D)] Γ(M, D) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, D) Γ(M, D) t) (bijective_smul_of_isFrameOn ht)
  let ρ : Γ(X, D) ≃ₗ[Γ(X, D)] Γ(L ⊗ M, D) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, D) Γ(L ⊗ M, D) (Scheme.Modules.tensorSections s t))
      hst
  have key : theta L M D ∘ₗ (TensorProduct.congr σ τ).toLinearMap =
      ρ.toLinearMap ∘ₗ (TensorProduct.lid Γ(X, D) Γ(X, D)).toLinearMap := by
    refine TensorProduct.ext' fun g h => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.congr_tmul, TensorProduct.lid_tmul,
      σ, τ, ρ, LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, theta_tmul,
      Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right, smul_eq_mul, mul_smul]
    exact smul_comm _ _ _
  have hθ : theta L M D = (ρ.toLinearMap ∘ₗ (TensorProduct.lid Γ(X, D) Γ(X, D)).toLinearMap) ∘ₗ
      (TensorProduct.congr σ τ).symm.toLinearMap := by
    rw [← key, LinearMap.comp_assoc]
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [hθ]
  exact (ρ.bijective.comp (TensorProduct.lid Γ(X, D) Γ(X, D)).bijective).comp
    (TensorProduct.congr σ τ).symm.bijective

theorem exists_basicOpen_isFrameOn (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    ∃ f : Γ(X, U), x ∈ X.basicOpen f ∧
      (∃ s : Γ(L, X.basicOpen f), Scheme.Modules.IsFrameOn s (X.basicOpen f)) ∧
      (∃ t : Γ(M, X.basicOpen f), Scheme.Modules.IsFrameOn t (X.basicOpen f)) := by
  obtain ⟨WL, hxL, ⟨eL⟩⟩ := hL.1 x
  obtain ⟨WM, hxM, ⟨eM⟩⟩ := hM.1 x
  obtain ⟨sL, hsL⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit WL eL
  obtain ⟨sM, hsM⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit WM eM
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, (⟨hxL, hxM⟩ : x ∈ WL ⊓ WM)⟩ : (WL ⊓ WM : X.Opens)) hx
  refine ⟨f, hxf, ⟨L.presheaf.map (homOfLE (hfle.trans inf_le_left)).op sL, ?_⟩,
    ⟨M.presheaf.map (homOfLE (hfle.trans inf_le_right)).op sM, ?_⟩⟩
  · exact (hsL.map (homOfLE (hfle.trans inf_le_left))).mono (hfle.trans inf_le_left)
  · exact (hsM.map (homOfLE (hfle.trans inf_le_right))).mono (hfle.trans inf_le_right)

end Frames

section Global

variable {L M : X.Modules}

theorem main (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M) (U : X.affineOpens) :
    Function.Bijective (theta L M U) := by

  let s : Set Γ(X, U) := {f | (∃ s : Γ(L, X.basicOpen f), Scheme.Modules.IsFrameOn s (X.basicOpen f)) ∧
    (∃ t : Γ(M, X.basicOpen f), Scheme.Modules.IsFrameOn t (X.basicOpen f))}
  have hspan : Ideal.span s = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, hxf, hfL, hfM⟩ := exists_basicOpen_isFrameOn hL hM (U : X.Opens) U.2 hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfL, hfM⟩, hxf⟩
  haveI hLM : Scheme.Modules.IsInvertible (L ⊗ M) := hL.tensor hM
  haveI : ∀ r : s, IsLocalizedModule.Away r.1 (resBO L (U : X.Opens) r.1) := fun r =>
    isLocalizedModule_resBO L U r.1 hL U.2
  haveI : ∀ r : s, IsLocalizedModule.Away r.1 (resBO M (U : X.Opens) r.1) := fun r =>
    isLocalizedModule_resBO M U r.1 hM U.2
  haveI : ∀ r : s, IsLocalizedModule.Away r.1 (resBO (L ⊗ M) (U : X.Opens) r.1) := fun r =>
    isLocalizedModule_resBO (L ⊗ M) U r.1 hLM U.2
  refine bijective_of_isLocalized_span s hspan
    (fun r : s => Γ(L, X.basicOpen r.1) ⊗[Γ(X, U)] Γ(M, X.basicOpen r.1))
    (fun r : s => TensorProduct.map (resBO L (U : X.Opens) r.1) (resBO M (U : X.Opens) r.1))
    (fun r : s => Γ(L ⊗ M, X.basicOpen r.1))
    (fun r : s => resBO (L ⊗ M) (U : X.Opens) r.1)
    (theta L M U) fun r => ?_

  have hmap : IsLocalizedModule.map (Submonoid.powers r.1)
      (TensorProduct.map (resBO L (U : X.Opens) r.1) (resBO M (U : X.Opens) r.1))
      (resBO (L ⊗ M) (U : X.Opens) r.1) (theta L M U) = thetaBO L M U r.1 := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r.1)
      (TensorProduct.map (resBO L (U : X.Opens) r.1) (resBO M (U : X.Opens) r.1))
      (f' := resBO (L ⊗ M) (U : X.Opens) r.1)
    rw [IsLocalizedModule.map_comp, thetaBO_comp_map]
  rw [hmap]
  obtain ⟨⟨sL, hsL⟩, ⟨sM, hsM⟩⟩ := r.2
  exact thetaBO_bijective_of L M U r.1 U.2 (theta_bijective_of_isFrameOn hsL hsM)

end Global

end P2mPicCompareSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin.P2mPicCompareSol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin.P2mPicCompareSol"

open P2mPicCompareSol in
theorem solution
    {X : Scheme.{u}} {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (U : X.affineOpens) :
    Function.Bijective (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U) :
      Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U)) :=
  P2mPicCompareSol.main hL hM U

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin (solution)
