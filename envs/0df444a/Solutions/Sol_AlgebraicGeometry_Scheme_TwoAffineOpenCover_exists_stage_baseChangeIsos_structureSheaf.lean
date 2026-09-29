-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3f61f91c-f8fe-5761-87fa-821dcc7bde45

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Theorems.Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry TensorProduct NeronModelInfra AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.appLE_comp_appLE Spec Scheme Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.ΓSpecIso RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf RelPicard.isPullback_baseChangeSnd Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd LFP.stageHom isPullback_baseChangeSnd"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom"
namespace StageTransport
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem appLE_congrHom {X Z : Scheme.{u}} {f g : X ⟶ Z} (e : f = g) (U : Z.Opens) (V : X.Opens)
    (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V h₁ = g.appLE U V h₂ := by
  subst e; rfl

variable {Y Y' : Scheme.{u}} (φ : Y' ⟶ Y) [IsIso φ] {W : Y.Opens} {W' : Y'.Opens} (hW : φ ⁻¹ᵁ W = W')

def transportIso : Γ(Y, W) ≅ Γ(Y', W') :=
  asIso (φ.app W) ≪≫ Y'.presheaf.mapIso (eqToIso hW.symm).op

theorem transportIso_hom : (transportIso φ hW).hom = φ.appLE W W' hW.ge := by
  change φ.app W ≫ Y'.presheaf.map (eqToHom hW.symm).op = φ.app W ≫ Y'.presheaf.map (homOfLE hW.ge).op
  exact congrArg (fun k : W' ⟶ φ ⁻¹ᵁ W => φ.app W ≫ Y'.presheaf.map k.op) (Subsingleton.elim _ _)

theorem transportIso_hom_apply (t : Γ(Y, W)) :
    (transportIso φ hW).hom.hom t = (φ.appLE W W' hW.ge).hom t := by
  rw [transportIso_hom]

variable {S : Type u} [CommRing S] (p : Y ⟶ Spec (.of S)) (p' : Y' ⟶ Spec (.of S)) (hφ : φ ≫ p = p')

def transportAlgEquiv :
    letI := algebraOfHom p W; letI := algebraOfHom p' W'
    Γ(Y, W) ≃ₐ[S] Γ(Y', W') :=
  letI := algebraOfHom p W; letI := algebraOfHom p' W'
  AlgEquiv.ofRingEquiv (f := (transportIso φ hW).commRingCatIsoToRingEquiv) (fun a => by
    change (transportIso φ hW).hom.hom ((p.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of S)).inv.hom a))
      = (p'.appLE ⊤ W' le_top).hom ((Scheme.ΓSpecIso (.of S)).inv.hom a)
    rw [transportIso_hom, ← CommRingCat.comp_apply (p.appLE ⊤ W le_top) (φ.appLE W W' hW.ge),
      Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun k : Γ(Spec (.of S), ⊤) ⟶ Γ(Y', W') => k.hom ((Scheme.ΓSpecIso (.of S)).inv.hom a))
      (appLE_congrHom hφ ⊤ W' _ _))

theorem transportAlgEquiv_apply (t : Γ(Y, W)) :
    letI := algebraOfHom p W; letI := algebraOfHom p' W'
    transportAlgEquiv φ hW p p' hφ t = (φ.appLE W W' hW.ge).hom t := by
  change (transportIso φ hW).hom.hom t = _
  rw [transportIso_hom]

include hφ in

theorem exists_transportAlgEquiv :
    letI := algebraOfHom p W; letI := algebraOfHom p' W'
    ∃ τ : Γ(Y, W) ≃ₐ[S] Γ(Y', W'), ∀ t, τ t = (φ.appLE W W' hW.ge).hom t :=
  ⟨transportAlgEquiv φ hW p p' hφ, transportAlgEquiv_apply φ hW p p' hφ⟩

end AlgebraicGeometry.RelPicard.LFP.StageTransport

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.appLE_comp_appLE Spec Scheme Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.ΓSpecIso RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf RelPicard.isPullback_baseChangeSnd Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd LFP.stageHom isPullback_baseChangeSnd"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom"
namespace Stage
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A'] [IsScalarTower R A₀ A']

abbrev CA (A : Type u) [CommRing A] [Algebra R A] : Scheme.{u} := pullback c (specMap R A)

abbrev prA (A : Type u) [CommRing A] [Algebra R A] : CA R c A ⟶ Spec (.of A) := pullback.snd c (specMap R A)

abbrev σ : CA R c A' ⟶ CA R c A₀ := RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))

theorem stageHom_toAlgHom_val :
    (stageHom R (IsScalarTower.toAlgHom R A₀ A')).1 = specMap A₀ A' := rfl

theorem hsq : IsPullback (σ R c A₀ A') (prA R c A') (prA R c A₀) (specMap A₀ A') :=
  RelPicard.isPullback_baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))

abbrev X' : Scheme.{u} := pullback (prA R c A₀) (specMap A₀ A')

def φ : CA R c A' ≅ X' R c A₀ A' := (hsq R c A₀ A').isoPullback

@[scoped simp] theorem φ_hom_fst : (φ R c A₀ A').hom ≫ pullback.fst (prA R c A₀) (specMap A₀ A') = σ R c A₀ A' :=
  (hsq R c A₀ A').isoPullback_hom_fst
@[scoped simp] theorem φ_hom_snd : (φ R c A₀ A').hom ≫ pullback.snd (prA R c A₀) (specMap A₀ A') = prA R c A' :=
  (hsq R c A₀ A').isoPullback_hom_snd
@[scoped simp] theorem φ_inv_σ : (φ R c A₀ A').inv ≫ σ R c A₀ A' = pullback.fst (prA R c A₀) (specMap A₀ A') :=
  (hsq R c A₀ A').isoPullback_inv_fst
@[scoped simp] theorem φ_inv_prA : (φ R c A₀ A').inv ≫ prA R c A' = pullback.snd (prA R c A₀) (specMap A₀ A') :=
  (hsq R c A₀ A').isoPullback_inv_snd

theorem φ_hom_preimage_fst_preimage (U : (CA R c A₀).Opens) :
    (φ R c A₀ A').hom ⁻¹ᵁ ((pullback.fst (prA R c A₀) (specMap A₀ A')) ⁻¹ᵁ U) = (σ R c A₀ A') ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, φ_hom_fst]

end AlgebraicGeometry.RelPicard.LFP.Stage
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP.Stage"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.appLE_comp_appLE Spec Scheme Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.ΓSpecIso RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf RelPicard.isPullback_baseChangeSnd Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd LFP.stageHom isPullback_baseChangeSnd"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom"
namespace Stage
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

open AlgebraicGeometry.RelPicard.LFP.StageTransport

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A'] [IsScalarTower R A₀ A']

abbrev fst' : X' R c A₀ A' ⟶ CA R c A₀ := pullback.fst (prA R c A₀) (specMap A₀ A')

abbrev snd' : X' R c A₀ A' ⟶ Spec (.of A') := pullback.snd (prA R c A₀) (specMap A₀ A')

theorem φ_hom_preimage_eq (U : (CA R c A₀).Opens) (U' : (CA R c A').Opens) (hU : (σ R c A₀ A') ⁻¹ᵁ U = U') :
    (φ R c A₀ A').hom ⁻¹ᵁ ((fst' R c A₀ A') ⁻¹ᵁ U) = U' := by
  rw [φ_hom_preimage_fst_preimage]; exact hU

theorem φ_appLE_fst_app (U : (CA R c A₀).Opens) (U' : (CA R c A').Opens) (hU : (σ R c A₀ A') ⁻¹ᵁ U = U')
    (h : U' ≤ (φ R c A₀ A').hom ⁻¹ᵁ ((fst' R c A₀ A') ⁻¹ᵁ U)) (s : Γ(CA R c A₀, U)) :
    ((φ R c A₀ A').hom.appLE ((fst' R c A₀ A') ⁻¹ᵁ U) U' h).hom (((fst' R c A₀ A').app U).hom s)
      = ((σ R c A₀ A').appLE U U' hU.ge).hom s := by
  rw [← CommRingCat.comp_apply ((fst' R c A₀ A').app U) ((φ R c A₀ A').hom.appLE _ U' h),
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun k : Γ(CA R c A₀, U) ⟶ Γ(CA R c A', U') => k.hom s)
    (appLE_congrHom (φ_hom_fst R c A₀ A') U U' _ _)

end AlgebraicGeometry.RelPicard.LFP.Stage
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP.Stage"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP.Stage"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP.Stage"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP.Stage"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.AlgebraicGeometry.RelPicard.LFP.Stage"

open AlgebraicGeometry.RelPicard.LFP.Stage AlgebraicGeometry.RelPicard.LFP.StageTransport

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A'] [IsScalarTower R A₀ A'] :
    ∃ (e0 : (A' ⊗[A₀] ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A0) ≃ₐ[A']
          ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A0)
      (e1 : (A' ⊗[A₀] ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A1) ≃ₐ[A']
          ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A1)
      (e01 : (A' ⊗[A₀] ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01) ≃ₐ[A']
          ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A01),
      (∀ s, e0 ((1 : A') ⊗ₜ[A₀] s) = ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U0)
          ((𝒱.pullback c A').U0) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) ∧
      (∀ s, e1 ((1 : A') ⊗ₜ[A₀] s) = ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U1)
          ((𝒱.pullback c A').U1) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) ∧
      (∀ s, e01 ((1 : A') ⊗ₜ[A₀] s) =
        ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1)
          ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) := by
  obtain ⟨e0, e1, e01, eH0, eH1, he0, he1, he01, -, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf
      (𝒱.pullback c A₀) (Limits.pullback.snd c (specMap R A₀)) A'
  have hU0 := baseChangeSnd_preimage_U0 𝒱 c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))
  have hU1 := baseChangeSnd_preimage_U1 𝒱 c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))
  have hU01 := baseChangeSnd_preimage_inf 𝒱 c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))
  obtain ⟨τ0, hτ0⟩ := exists_transportAlgEquiv (φ R c A₀ A').hom
    (W := (fst' R c A₀ A') ⁻¹ᵁ (𝒱.pullback c A₀).U0) (W' := (𝒱.pullback c A').U0)
    (φ_hom_preimage_eq R c A₀ A' _ _ hU0) (snd' R c A₀ A') (prA R c A') (φ_hom_snd R c A₀ A')
  obtain ⟨τ1, hτ1⟩ := exists_transportAlgEquiv (φ R c A₀ A').hom
    (W := (fst' R c A₀ A') ⁻¹ᵁ (𝒱.pullback c A₀).U1) (W' := (𝒱.pullback c A').U1)
    (φ_hom_preimage_eq R c A₀ A' _ _ hU1) (snd' R c A₀ A') (prA R c A') (φ_hom_snd R c A₀ A')
  obtain ⟨τ01, hτ01⟩ := exists_transportAlgEquiv (φ R c A₀ A').hom
    (W := (fst' R c A₀ A') ⁻¹ᵁ ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1))
    (W' := (𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1)
    (φ_hom_preimage_eq R c A₀ A' _ _ hU01) (snd' R c A₀ A') (prA R c A') (φ_hom_snd R c A₀ A')
  refine ⟨e0.trans τ0, e1.trans τ1, e01.trans τ01, fun s => ?_, fun s => ?_, fun s => ?_⟩
  · rw [AlgEquiv.trans_apply, he0]
    exact (hτ0 _).trans (φ_appLE_fst_app R c A₀ A' _ _ hU0 _ s)
  · rw [AlgEquiv.trans_apply, he1]
    exact (hτ1 _).trans (φ_appLE_fst_app R c A₀ A' _ _ hU1 _ s)
  · rw [AlgEquiv.trans_apply, he01]
    exact (hτ01 _).trans (φ_appLE_fst_app R c A₀ A' _ _ hU01 _ s)

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf (solution)
