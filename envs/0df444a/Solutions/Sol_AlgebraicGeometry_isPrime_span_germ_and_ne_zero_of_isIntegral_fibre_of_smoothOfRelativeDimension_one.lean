-- Prove2me | solution 1 for AlgebraicGeometry.isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2f046a56-c227-5b79-910f-8ac40fdc7150

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE SmoothOfRelativeDimension.smooth Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd SmoothOfRelativeDimension Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec IsIntegral Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen Smooth.smooth_appLE pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.germ_stalkMap Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE IsIntegral.component_integral Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Opens.topIso_inv Hom mk Γ topIso_hom topIso ΓSpecIso_inv_naturality isoSpec_Spec_inv Opens.topIso_hom Hom.comp_appTop isoSpec Opens residue Hom.appLE_map Hom.app_eq_appLE Hom.germ_stalkMap Opens.ι_appTop Hom.appLE ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.algebraOfHom"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom algebraMap_algebraOfHom pullback mk"
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

end

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one.AlgebraicGeometry TensorProduct"

namespace Ideal p2m_export "Ideal" "Quotient.eq_zero_iff_mem map_span primeCompl span isDomain IsMaximal Quotient.mk Quotient.field map Quotient.lift_mk span_singleton_le_iff_mem IsPrime Quotient.lift span_le map_top mem_span_singleton_self" end Ideal
p2m_open_scoped "Ideal" in

theorem Ideal.isPrime_span_algebraMap_of_isDomain_tensor
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {κ : Type*} [Field κ] [Algebra R κ]
    (ϖ : R) (hker : RingHom.ker (algebraMap R κ) = Ideal.span {ϖ}) (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    [IsDomain (κ ⊗[R] A)] : (Ideal.span {algebraMap R A ϖ} : Ideal A).IsPrime := by
  classical
  set I : Ideal R := Ideal.span {ϖ} with hI
  haveI : I.IsMaximal := hmax
  letI : Field (R ⧸ I) := Ideal.Quotient.field I

  let qk : R ⧸ I →+* κ := Ideal.Quotient.lift I (algebraMap R κ) (fun r hr => by
    rwa [← RingHom.mem_ker, hker])
  letI : Algebra (R ⧸ I) κ := qk.toAlgebra
  haveI : IsScalarTower R (R ⧸ I) κ :=
    IsScalarTower.of_algebraMap_eq (fun r => (Ideal.Quotient.lift_mk I _ _).symm)

  let g : A →ₐ[R] κ ⊗[R] A := Algebra.TensorProduct.includeRight
  have hP : (RingHom.ker g).IsPrime := RingHom.ker_isPrime _
  suffices h : RingHom.ker g = Ideal.span {algebraMap R A ϖ} by rwa [← h]
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    change (1 : κ) ⊗ₜ[R] a = 0 at ha

    let e1 : (A ⧸ I.map (algebraMap R A)) ≃ₐ[A] A ⊗[R] (R ⧸ I) :=
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I
    let e2 : A ⊗[R] (R ⧸ I) ≃ₐ[R] (R ⧸ I) ⊗[R] A := Algebra.TensorProduct.comm R A (R ⧸ I)
    let j : (R ⧸ I) ⊗[R] A →ₐ[R ⧸ I] κ ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] A) := Algebra.TensorProduct.includeRight
    haveI : Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] A) := Module.Free.of_divisionRing _ _
    have hj : Function.Injective j := Algebra.TensorProduct.includeRight_injective qk.injective
    let e3 : κ ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] A) ≃ₗ[κ] κ ⊗[R] A :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) κ κ A

    have hcomp : ∀ b : A, e3 (j (e2 (e1 (Ideal.Quotient.mk _ b)))) = (1 : κ) ⊗ₜ[R] b := by
      intro b
      have h1 : e1 (Ideal.Quotient.mk _ b) = b ⊗ₜ[R] (1 : R ⧸ I) :=
        Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk A I b
      rw [h1]
      change e3 ((1 : κ) ⊗ₜ[R ⧸ I] (Algebra.TensorProduct.comm R A (R ⧸ I) (b ⊗ₜ[R] (1 : R ⧸ I)))) = _
      rw [Algebra.TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have h0 : e3 (j (e2 (e1 (Ideal.Quotient.mk _ a)))) = 0 := by rw [hcomp, ha]
    rw [LinearEquiv.map_eq_zero_iff, ← map_zero j, hj.eq_iff, EmbeddingLike.map_eq_zero_iff,
      EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.map_span, Set.image_singleton] at h0
    exact h0
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change (1 : κ) ⊗ₜ[R] (algebraMap R A ϖ) = 0
    have hϖ0 : algebraMap R κ ϖ = 0 := by
      rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ϖ
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, hϖ0,
      TensorProduct.zero_tmul]

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE SmoothOfRelativeDimension.smooth Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd SmoothOfRelativeDimension Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec IsIntegral Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen Smooth.smooth_appLE pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.germ_stalkMap Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE IsIntegral.component_integral Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom"
namespace GermToChart
p2m_open "AlgebraicGeometry"

theorem not_isUnit_germ_of_mem_fibre
    {R : Type u} [CommRing R] (ϖ : R) {κ : Type u} [Field κ] (q : R →+* κ) (hq : q ϖ = 0)
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
    (y : ↥(Limits.pullback c (Spec.map (CommRingCat.ofHom q)))) :
    ¬ IsUnit ((X.presheaf.germ ⊤ ((Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base y) trivial).hom
      (c.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom ϖ))) := by
  set F := Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q)) with hF
  set G := Limits.pullback.snd c (Spec.map (CommRingCat.ofHom q)) with hG
  intro hu

  have h1 := hu.map (F.stalkMap y).hom
  have h2 : (F.stalkMap y).hom ((X.presheaf.germ ⊤ (F.base y) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom ϖ))) =
      ((Limits.pullback c (Spec.map (CommRingCat.ofHom q))).presheaf.germ ⊤ y trivial).hom
        ((F ≫ c).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom ϖ)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap F ⊤ y trivial, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    rfl
  have h3 : (F ≫ c).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom ϖ) = 0 := by
    rw [Limits.pullback.condition, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    have h := congrArg (fun φ => φ.hom ϖ) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    rw [← h, hq, map_zero, map_zero]
  rw [h2, h3, map_zero] at h1
  exact not_isUnit_zero h1

end AlgebraicGeometry.GermToChart

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    {κ : Type u} [Field κ] (q : R →+* κ) (hker : RingHom.ker q = Ideal.span {ϖ})
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [IsIntegral X] [SmoothOfRelativeDimension 1 c]
    [IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q)))]
    (x : X) (hx : x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base) :
    (Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))}).IsPrime ∧
      (X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) ≠ 0 := by
  classical
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  letI algRκ : Algebra R κ := q.toAlgebra
  have hkerA : RingHom.ker (algebraMap R κ) = Ideal.span {ϖ} := hker
  have hqϖ : q ϖ = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ϖ

  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨xU, rfl⟩ : ∃ xU : U, (xU : X) = x := ⟨⟨x, hxU⟩, rfl⟩
  obtain ⟨y, hy⟩ := hx
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk (xU : X)) (hU.primeIdealOf xU).asIdeal :=
    hU.isLocalization_stalk xU
  set 𝔭 : Ideal Γ(X, U) := (hU.primeIdealOf xU).asIdeal with h𝔭

  set ϖx := (X.presheaf.germ ⊤ (xU : X) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) with hϖx
  have hϖA : algebraMap Γ(X, U) (X.presheaf.stalk (xU : X)) (algebraMap R Γ(X, U) ϖ) = ϖx := by
    change (X.presheaf.germ U (xU : X) xU.2).hom ((c.app ⊤ ≫ X.presheaf.map (homOfLE le_top).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) = _
    rw [CommRingCat.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) (xU : X) xU.2 _

  have hnu : ¬ IsUnit ϖx := by
    have h := AlgebraicGeometry.GermToChart.not_isUnit_germ_of_mem_fibre ϖ q hqϖ c y
    rwa [hy] at h

  haveI : Algebra.Smooth R Γ(X, U) := by
    have h1 : (c.appLE ⊤ U le_top).hom.Smooth :=
      Smooth.smooth_appLE (f := c) (isAffineOpen_top (Spec (.of R))) hU le_top
    have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom.Smooth := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.Smooth.respectsIso.cancel_left_isIso _ _).mpr h1
    exact h2
  haveI : Module.Flat R Γ(X, U) := inferInstance

  haveI hint : IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R κ)) :=
    inferInstanceAs (IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q))))
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R κ))
    ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R κ)) ⁻¹ᵁ U)
  obtain ⟨e, -⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_algEquiv_sections_baseChange c U hU κ
  haveI : IsDomain Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R κ),
      (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R κ)) ⁻¹ᵁ U) :=
    @IsIntegral.component_integral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R κ)) hint _
      ⟨⟨y, show (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R κ)).base y ∈ U by rw [show
        (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R κ)).base y = (xU : X) from hy]; exact xU.2⟩⟩
  haveI : IsDomain (κ ⊗[R] Γ(X, U)) := MulEquiv.isDomain _ e.toMulEquiv
  have hprimeA : (Ideal.span {algebraMap R Γ(X, U) ϖ} : Ideal Γ(X, U)).IsPrime :=
    Ideal.isPrime_span_algebraMap_of_isDomain_tensor ϖ hkerA hmax

  have hϖ𝔭 : algebraMap R Γ(X, U) ϖ ∈ 𝔭 := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (xU : X)) 𝔭, hϖA, IsLocalRing.mem_maximalIdeal]
    exact hnu
  have hmap : Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk (xU : X))) (Ideal.span {algebraMap R Γ(X, U) ϖ}) =
      Ideal.span {ϖx} := by
    rw [Ideal.map_span, Set.image_singleton, hϖA]
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    refine IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl (X.presheaf.stalk (xU : X)) _ hprimeA ?_
    rw [Set.disjoint_left]
    intro a ha hmem
    exact ha ((Ideal.span_singleton_le_iff_mem 𝔭).mpr hϖ𝔭 hmem)
  ·
    intro h0
    rw [← hϖA, IsLocalization.map_eq_zero_iff 𝔭.primeCompl (X.presheaf.stalk (xU : X))] at h0
    obtain ⟨m, hm⟩ := h0
    haveI : Nonempty U := ⟨xU⟩
    have hm0 : (m : Γ(X, U)) ≠ 0 := fun h => m.2 (h ▸ 𝔭.zero_mem)
    have hϖ0 : algebraMap R Γ(X, U) ϖ = 0 := (mul_eq_zero.mp hm).resolve_left hm0
    have hreg : IsSMulRegular Γ(X, U) ϖ := Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ)
    have h1 : ϖ • (1 : Γ(X, U)) = ϖ • 0 := by rw [Algebra.smul_def, mul_one, hϖ0, smul_zero]
    exact one_ne_zero (hreg h1)

end S_AlgebraicGeometry_isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one (solution)
