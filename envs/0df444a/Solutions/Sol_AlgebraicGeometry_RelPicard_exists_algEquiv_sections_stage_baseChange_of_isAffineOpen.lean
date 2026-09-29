-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_algEquiv_sections_stage_baseChange_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ba46d8b8-7129-5bbf-9f5b-fc3beebea777

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Theorems.Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry TensorProduct NeronModelInfra AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Γ IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop IsAffineOpen.isoSpec pullbackSpecIso_inv_fst isAffineOpen_top IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.baseChangeSnd RelPicard.LFP.stageHom RelPicard.isPullback_baseChangeSnd"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Opens.topIso_inv Hom Hom.appLE_comp_appLE Γ topIso_hom topIso ΓSpecIso_inv_naturality isoSpec_Spec_inv Opens.topIso_hom Hom.comp_appTop isoSpec Opens Hom.appLE_map Hom.app_eq_appLE Hom.comp_preimage Opens.ι_appTop Hom.appLE ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.algebraOfHom"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom algebraMap_algebraOfHom pullback"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace AffineBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
variable (A : Type u) [CommRing A] [Algebra R A]

abbrev XA : Scheme.{u} := Limits.pullback c (specMap R A)

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.fst : XA c A ⟶ X := Limits.pullback.fst c (specMap R A)
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange" "fst"

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.snd : XA c A ⟶ Spec (.of A) := Limits.pullback.snd c (specMap R A)

p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange" "snd"
variable (U : X.Opens) (hU : IsAffineOpen U)

theorem specMap_algebraMap_eq :
    letI := algebraOfHom c U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ c := by
  letI := algebraOfHom c U
  have halg : (algebraMap R Γ(X, U)) = ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom := rfl
  rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top (Spec (.of R))) hU (le_top : U ≤ c ⁻¹ᵁ ⊤)]

def pullbackAffineOpenIsoSpecTensor :
    letI := algebraOfHom c U
    ((fst c A) ⁻¹ᵁ U).toScheme ≅ Spec (.of (Γ(X, U) ⊗[R] A)) :=
  letI := algebraOfHom c U
  (pullbackRestrictIsoRestrict (fst c A) U).symm
    ≪≫ pullbackSymmetry _ _
    ≪≫ pullbackRightPullbackFstIso c (specMap R A) U.ι
    ≪≫ asIso (pullback.map (U.ι ≫ c) (specMap R A)
        (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) (specMap R A)
        hU.isoSpec.hom (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, specMap_algebraMap_eq c U hU, ← hU.isoSpec_inv_ι_assoc, Iso.hom_inv_id_assoc])
        (by rw [Category.id_comp, Category.comp_id]))
    ≪≫ pullbackSpecIso R Γ(X, U) A

def sigma :
    letI := algebraOfHom c U
    (Γ(X, U) ⊗[R] A) ≃+* Γ(XA c A, (fst c A) ⁻¹ᵁ U) :=
  letI := algebraOfHom c U
  ((Scheme.ΓSpecIso (.of (Γ(X, U) ⊗[R] A))).symm
    ≪≫ Scheme.Γ.mapIso (pullbackAffineOpenIsoSpecTensor c A U hU).op
    ≪≫ ((fst c A) ⁻¹ᵁ U).topIso).commRingCatIsoToRingEquiv

theorem sigma_apply (x : letI := algebraOfHom c U; Γ(X, U) ⊗[R] A) :
    letI := algebraOfHom c U
    sigma c A U hU x = ((Scheme.ΓSpecIso (.of (Γ(X, U) ⊗[R] A))).inv
      ≫ (pullbackAffineOpenIsoSpecTensor c A U hU).hom.appTop ≫ ((fst c A) ⁻¹ᵁ U).topIso.hom).hom x :=
  rfl

theorem iso_hom_comp_sndLeg :
    letI := algebraOfHom c U
    ((fst c A) ⁻¹ᵁ U).ι ≫ snd c A
      = (pullbackAffineOpenIsoSpecTensor c A U hU).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] Γ(X, U) ⊗[R] A)) := by
  letI := algebraOfHom c U
  rw [pullbackAffineOpenIsoSpecTensor, ← pullbackSpecIso_inv_snd R Γ(X, U) A]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc, pullbackRestrictIsoRestrict_inv_fst_assoc]

theorem iso_hom_comp_fstLeg :
    letI := algebraOfHom c U
    (pullbackAffineOpenIsoSpecTensor c A U hU).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X, U) ⊗[R] A))
      = ((fst c A) ∣_ U) ≫ hU.isoSpec.hom := by
  letI := algebraOfHom c U
  rw [pullbackAffineOpenIsoSpecTensor, ← pullbackSpecIso_inv_fst R Γ(X, U) A]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc]
  rfl

omit [CommRing R] in
theorem opens_ι_appTop_topIso_hom {Y : Scheme.{u}} (V : Y.Opens) :
    V.ι.appTop ≫ V.topIso.hom = Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact (Y.presheaf.map_comp _ _).symm.trans (congrArg Y.presheaf.map (Subsingleton.elim _ _))

omit [CommRing R] in
theorem topIso_morphismRestrict_appTop_topIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) (W : Z.Opens) :
    W.topIso.inv ≫ (g ∣_ W).appTop ≫ (g ⁻¹ᵁ W).topIso.hom = g.app W := by
  simp only [Scheme.Opens.topIso_inv, eqToHom_op, TopologicalSpace.Opens.map_top,
    Scheme.Opens.topIso_hom, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE]
  erw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem sigma_tmul_one (s : Γ(X, U)) :
    letI := algebraOfHom c U
    sigma c A U hU (s ⊗ₜ[R] (1 : A)) = ((fst c A).app U).hom s := by
  letI := algebraOfHom c U
  rw [sigma_apply]
  have hiL : s ⊗ₜ[R] (1 : A)
      = (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X, U) ⊗[R] A)).hom s := rfl
  rw [hiL, ← CommRingCat.comp_apply, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Category.assoc _ _ (((fst c A) ⁻¹ᵁ U).topIso.hom), ← Scheme.Hom.comp_appTop,
    iso_hom_comp_fstLeg c A U hU, Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
  have hΓ : (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv ≫ (Scheme.ΓSpecIso Γ(X, U)).hom = 𝟙 _ :=
    Iso.inv_hom_id _
  simp only [← Category.assoc]
  rw [hΓ, Category.id_comp, Category.assoc, topIso_morphismRestrict_appTop_topIso]

theorem sigma_one_tmul (a : A) :
    letI := algebraOfHom c U
    sigma c A U hU ((1 : Γ(X, U)) ⊗ₜ[R] a)
      = ((XA c A).presheaf.map (homOfLE (le_top : (fst c A) ⁻¹ᵁ U ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ (snd c A).appTop).hom a) := by
  letI := algebraOfHom c U
  rw [sigma_apply]
  have hiR : (1 : Γ(X, U)) ⊗ₜ[R] a
      = (CommRingCat.ofHom (R := A) (S := Γ(X, U) ⊗[R] A)
          (Algebra.TensorProduct.includeRight : A →ₐ[R] Γ(X, U) ⊗[R] A)).hom a := rfl
  rw [hiR, ← CommRingCat.comp_apply, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Category.assoc _ _ (((fst c A) ⁻¹ᵁ U).topIso.hom), ← Scheme.Hom.comp_appTop,
    ← iso_hom_comp_sndLeg c A U hU, Scheme.Hom.comp_appTop, Category.assoc,
    opens_ι_appTop_topIso_hom ((fst c A) ⁻¹ᵁ U)]
  rfl

theorem algebraMap_sndAlgebra (a : A) :
    (algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)).algebraMap a
      = ((XA c A).presheaf.map (homOfLE (le_top : (fst c A) ⁻¹ᵁ U ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ (snd c A).appTop).hom a) := by
  rw [algebraMap_algebraOfHom, Scheme.Hom.appLE, CommRingCat.comp_apply, CommRingCat.comp_apply]
  rfl

def algEquiv :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    (A ⊗[R] Γ(X, U)) ≃ₐ[A] Γ(XA c A, (fst c A) ⁻¹ᵁ U) :=
  letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R A Γ(X, U)).toRingEquiv.trans (sigma c A U hU))
    (fun a => by
      show sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) (algebraMap A (A ⊗[R] Γ(X, U)) a)) = _
      rw [Algebra.TensorProduct.algebraMap_apply, show algebraMap A A a = a from rfl,
        Algebra.TensorProduct.comm_tmul, sigma_one_tmul, algebraMap_sndAlgebra])

theorem algEquiv_one_tmul (s : Γ(X, U)) :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    algEquiv c A U hU ((1 : A) ⊗ₜ[R] s) = ((fst c A).app U).hom s := by
  letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  show sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) ((1 : A) ⊗ₜ[R] s)) = _
  rw [Algebra.TensorProduct.comm_tmul, sigma_tmul_one]

end AffineBaseChange

open AffineBaseChange in

theorem exists_algEquiv_sections_baseChange {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (U : X.Opens) (hU : IsAffineOpen U) (A : Type u) [CommRing A] [Algebra R A] :
    letI := algebraOfHom c U
    letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) ((Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ U)
    ∃ e : (A ⊗[R] Γ(X, U)) ≃ₐ[A]
        Γ(Limits.pullback c (specMap R A), (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ U),
      ∀ s : Γ(X, U), e ((1 : A) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R A)).app U).hom s :=
  ⟨algEquiv c A U hU, algEquiv_one_tmul c A U hU⟩

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Γ IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop IsAffineOpen.isoSpec pullbackSpecIso_inv_fst isAffineOpen_top IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.baseChangeSnd RelPicard.LFP.stageHom RelPicard.isPullback_baseChangeSnd"
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
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Γ IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop IsAffineOpen.isoSpec pullbackSpecIso_inv_fst isAffineOpen_top IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.baseChangeSnd RelPicard.LFP.stageHom RelPicard.isPullback_baseChangeSnd"
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP.Stage"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Γ IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop IsAffineOpen.isoSpec pullbackSpecIso_inv_fst isAffineOpen_top IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.comp_preimage Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.baseChangeSnd RelPicard.LFP.stageHom RelPicard.isPullback_baseChangeSnd"
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP.Stage"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP.Stage"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP.Stage"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP.Stage"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.AlgebraicGeometry.RelPicard.LFP.Stage"

open AlgebraicGeometry.RelPicard.LFP.Stage AlgebraicGeometry.RelPicard.LFP.StageTransport

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A'] [IsScalarTower R A₀ A']
    (U : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Opens) (hU : IsAffineOpen U)
    (U' : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A')).Opens)
    (hU' : RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')) ⁻¹ᵁ U = U') :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) U'
    ∃ e : (A' ⊗[A₀] Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀), U)) ≃ₐ[A']
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), U'),
      ∀ s, e ((1 : A') ⊗ₜ[A₀] s) =
        ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE U U' hU'.ge).hom s := by
  letI iU := Scheme.TwoAffineOpenCover.algebraOfHom (prA R c A₀) U
  letI iU' := Scheme.TwoAffineOpenCover.algebraOfHom (prA R c A') U'
  letI iW := Scheme.TwoAffineOpenCover.algebraOfHom (snd' R c A₀ A') ((fst' R c A₀ A') ⁻¹ᵁ U)
  obtain ⟨e, he⟩ :=
    Scheme.TwoAffineOpenCover.exists_algEquiv_sections_baseChange (prA R c A₀) U hU A'
  obtain ⟨τ, hτ⟩ := exists_transportAlgEquiv (φ R c A₀ A').hom
    (W := (fst' R c A₀ A') ⁻¹ᵁ U) (W' := U')
    (φ_hom_preimage_eq R c A₀ A' U U' hU') (snd' R c A₀ A') (prA R c A') (φ_hom_snd R c A₀ A')
  refine ⟨e.trans τ, fun s => ?_⟩
  rw [AlgEquiv.trans_apply, he]
  exact (hτ _).trans (φ_appLE_fst_app R c A₀ A' U U' hU' _ s)

end S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen (solution)
