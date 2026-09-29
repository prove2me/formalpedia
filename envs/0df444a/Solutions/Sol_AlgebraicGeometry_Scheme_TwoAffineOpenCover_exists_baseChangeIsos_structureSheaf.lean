-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/287b85b5-8252-5765-8972-aa123be631af

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Scheme.Hom.naturality pullbackSpecIso_inv_fst isAffineOpen_top IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Opens.topIso_inv Hom mk Γ topIso_hom topIso ΓSpecIso_inv_naturality isoSpec_Spec_inv Opens.topIso_hom Hom.comp_appTop isoSpec Hom.naturality mk.injEq Opens Hom.appLE_map Hom.app_eq_appLE Opens.ι_appTop restrict Hom.appLE Cover ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.specMap"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom algebraMap_algebraOfHom restrictAlgHom cover structureSheafSections pullback isAffineOpen_U0 isAffineOpen_inf mk.injEq U1 U0 mk isAffineOpen_U1"
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

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Scheme.Hom.naturality pullbackSpecIso_inv_fst isAffineOpen_top IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Opens.topIso_inv Hom mk Γ topIso_hom topIso ΓSpecIso_inv_naturality isoSpec_Spec_inv Opens.topIso_hom Hom.comp_appTop isoSpec Hom.naturality mk.injEq Opens Hom.appLE_map Hom.app_eq_appLE Opens.ι_appTop restrict Hom.appLE Cover ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.specMap"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom algebraMap_algebraOfHom restrictAlgHom cover structureSheafSections pullback isAffineOpen_U0 isAffineOpen_inf mk.injEq U1 U0 mk isAffineOpen_U1"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace CechBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
variable (A : Type u) [CommRing A] [Algebra R A]

abbrev XA : Scheme.{u} := Limits.pullback c (specMap R A)

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.CechBaseChange.fst : XA c A ⟶ X := Limits.pullback.fst c (specMap R A)
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.CechBaseChange" "fst"

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.CechBaseChange.snd : XA c A ⟶ Spec (.of A) := Limits.pullback.snd c (specMap R A)

p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.CechBaseChange" "snd"

theorem restrict_compat {U V : X.Opens} (hVU : V ≤ U)
    (eU : letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
      (A ⊗[R] Γ(X, U)) ≃ₐ[A] Γ(XA c A, (fst c A) ⁻¹ᵁ U))
    (heU : letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
      ∀ s : Γ(X, U), eU ((1 : A) ⊗ₜ[R] s) = ((fst c A).app U).hom s)
    (eV : letI := algebraOfHom c V; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ V)
      (A ⊗[R] Γ(X, V)) ≃ₐ[A] Γ(XA c A, (fst c A) ⁻¹ᵁ V))
    (heV : letI := algebraOfHom c V; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ V)
      ∀ s : Γ(X, V), eV ((1 : A) ⊗ₜ[R] s) = ((fst c A).app V).hom s)
    (x : letI := algebraOfHom c U; A ⊗[R] Γ(X, U)) :
    letI := algebraOfHom c U; letI := algebraOfHom c V
    letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U); letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ V)
    eV ((restrictAlgHom c hVU).toLinearMap.baseChange A x)
      = ((XA c A).presheaf.map (homOfLE ((fst c A).preimage_mono hVU)).op).hom (eU x) := by
  letI := algebraOfHom c U; letI := algebraOfHom c V
  letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U); letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ V)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    have ha : a ⊗ₜ[R] s = a • ((1 : A) ⊗ₜ[R] s) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply, ha, map_smul, heU]
    have ha' : a ⊗ₜ[R] (restrictAlgHom c hVU s) = a • ((1 : A) ⊗ₜ[R] (restrictAlgHom c hVU s)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ha', map_smul, heV]

    have hnat : ((fst c A).app V).hom (restrictAlgHom c hVU s)
        = ((XA c A).presheaf.map (homOfLE ((fst c A).preimage_mono hVU)).op).hom (((fst c A).app U).hom s) := by
      change (X.presheaf.map (homOfLE hVU).op ≫ (fst c A).app V).hom s = _
      rw [Scheme.Hom.naturality]
      rfl
    rw [hnat, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

    change ((snd c A).appLE ⊤ ((fst c A) ⁻¹ᵁ V) le_top).hom _
      = ((XA c A).presheaf.map _).hom (((snd c A).appLE ⊤ ((fst c A) ⁻¹ᵁ U) le_top).hom _)
    rw [← CommRingCat.comp_apply _ ((XA c A).presheaf.map _), Scheme.Hom.appLE_map]

section Cech

variable (𝒱 : X.TwoAffineOpenCover)

abbrev SA : TwoChartCech.Sections ((𝒱.pullback c A).cover (snd c A)) :=
  (𝒱.pullback c A).structureSheafSections (snd c A)

structure BaseChangeIsos where
  e0 : (A ⊗[R] (𝒱.cover c).A0) ≃ₐ[A] ((𝒱.pullback c A).cover (snd c A)).A0
  e1 : (A ⊗[R] (𝒱.cover c).A1) ≃ₐ[A] ((𝒱.pullback c A).cover (snd c A)).A1
  e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A] ((𝒱.pullback c A).cover (snd c A)).A01
  he0 : ∀ s : (𝒱.cover c).A0, e0 ((1 : A) ⊗ₜ[R] s) = ((fst c A).app 𝒱.U0).hom s
  he1 : ∀ s : (𝒱.cover c).A1, e1 ((1 : A) ⊗ₜ[R] s) = ((fst c A).app 𝒱.U1).hom s
  he01 : ∀ s : (𝒱.cover c).A01, e01 ((1 : A) ⊗ₜ[R] s) = ((fst c A).app (𝒱.U0 ⊓ 𝒱.U1)).hom s

namespace BaseChangeIsos

variable {c A 𝒱} (E : BaseChangeIsos c A 𝒱)

theorem e01_ρ0 (x : A ⊗[R] (𝒱.cover c).A0) :
    E.e01 ((𝒱.cover c).ρ0.toLinearMap.baseChange A x) = ((𝒱.pullback c A).cover (snd c A)).ρ0 (E.e0 x) :=
  restrict_compat c A (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0) E.e0 E.he0 E.e01 E.he01 x

theorem e01_ρ1 (x : A ⊗[R] (𝒱.cover c).A1) :
    E.e01 ((𝒱.cover c).ρ1.toLinearMap.baseChange A x) = ((𝒱.pullback c A).cover (snd c A)).ρ1 (E.e1 x) :=
  restrict_compat c A (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1) E.e1 E.he1 E.e01 E.he01 x

theorem cechDiff_structureSheaf_apply {R' : Type u} [CommRing R'] (𝒰 : TwoChartCech.Cover.{u, u} R')
    (s : 𝒰.A0 × 𝒰.A1) : 𝒰.structureSheaf.cechDiff s = 𝒰.ρ1 s.2 - 𝒰.ρ0 s.1 := by
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r1_apply,
    TwoChartCech.Cover.lineBundle_r0_apply, Units.val_one, one_mul]

theorem e01_cechDiff_baseChange (x : A ⊗[R] ((𝒱.cover c).A0 × (𝒱.cover c).A1)) :
    E.e01 (((𝒱.structureSheafSections c).cechDiff.baseChange A) x)
      = (SA c A 𝒱).cechDiff
          (E.e0 (TensorProduct.prodRight R A A _ _ x).1, E.e1 (TensorProduct.prodRight R A A _ _ x).2) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Prod.fst_zero, Prod.snd_zero]; rw [Prod.mk_zero_zero, map_zero]
  | add x y hx hy =>
    simp only [map_add, Prod.fst_add, Prod.snd_add, hx, hy]
    rw [← map_add]; rfl
  | tmul a s =>
    rw [LinearMap.baseChange_tmul, cechDiff_structureSheaf_apply, TensorProduct.prodRight_tmul,
      cechDiff_structureSheaf_apply, TensorProduct.tmul_sub, map_sub]
    have h1 := E.e01_ρ1 (a ⊗ₜ[R] s.2)
    have h0 := E.e01_ρ0 (a ⊗ₜ[R] s.1)
    rw [LinearMap.baseChange_tmul] at h1 h0
    exact congrArg₂ (· - ·) h1 h0

theorem mem_ker_baseChange_iff (x : A ⊗[R] ((𝒱.cover c).A0 × (𝒱.cover c).A1)) :
    x ∈ LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A)
      ↔ (E.e0 (TensorProduct.prodRight R A A _ _ x).1, E.e1 (TensorProduct.prodRight R A A _ _ x).2)
          ∈ (SA c A 𝒱).H0 := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← e01_cechDiff_baseChange,
    ← map_zero E.e01, E.e01.injective.eq_iff]

def pairMap : (A ⊗[R] ((𝒱.cover c).A0 × (𝒱.cover c).A1)) →ₗ[A]
    (((𝒱.pullback c A).cover (snd c A)).A0 × ((𝒱.pullback c A).cover (snd c A)).A1) :=
  (E.e0.toLinearEquiv.toLinearMap.prodMap E.e1.toLinearEquiv.toLinearMap) ∘ₗ
    (TensorProduct.prodRight R A A _ _).toLinearMap

theorem pairMap_apply (x : A ⊗[R] ((𝒱.cover c).A0 × (𝒱.cover c).A1)) :
    E.pairMap x = (E.e0 (TensorProduct.prodRight R A A _ _ x).1, E.e1 (TensorProduct.prodRight R A A _ _ x).2) :=
  rfl

theorem pairMap_bijective : Function.Bijective E.pairMap := by
  constructor
  · intro x y h
    apply (TensorProduct.prodRight R A A _ _).injective
    rw [pairMap_apply, pairMap_apply, Prod.mk.injEq] at h
    exact Prod.ext (E.e0.injective h.1) (E.e1.injective h.2)
  · rintro ⟨p0, p1⟩
    obtain ⟨x0, rfl⟩ := E.e0.surjective p0
    obtain ⟨x1, rfl⟩ := E.e1.surjective p1
    refine ⟨(TensorProduct.prodRight R A A _ _).symm (x0, x1), ?_⟩
    rw [pairMap_apply, LinearEquiv.apply_symm_apply]

def kerToH0 : LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A) →ₗ[A] (SA c A 𝒱).H0 :=
  E.pairMap.restrict fun x hx => by rw [pairMap_apply]; exact (E.mem_ker_baseChange_iff x).mp hx

theorem kerToH0_bijective : Function.Bijective E.kerToH0 := by
  constructor
  · intro x y h
    exact Subtype.ext (E.pairMap_bijective.1 (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := E.pairMap_bijective.2 y
    exact ⟨⟨x, (E.mem_ker_baseChange_iff x).mpr (by rwa [pairMap_apply] at hy)⟩, rfl⟩

def kerEquivH0 : LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A) ≃ₗ[A] (SA c A 𝒱).H0 :=
  LinearEquiv.ofBijective _ E.kerToH0_bijective

theorem kerEquivH0_apply_coe (x : LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A)) :
    ((E.kerEquivH0 x : (SA c A 𝒱).M0 × (SA c A 𝒱).M1))
      = (E.e0 (TensorProduct.prodRight R A A _ _ x.1).1, E.e1 (TensorProduct.prodRight R A A _ _ x.1).2) :=
  rfl

def cokerEquivH1 :
    ((A ⊗[R] (𝒱.cover c).A01) ⧸ LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange A))
      ≃ₗ[A] (SA c A 𝒱).H1 :=
  Submodule.Quotient.equiv _ _ E.e01.toLinearEquiv (by
    apply le_antisymm
    · rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
      refine ⟨E.pairMap x, ?_⟩
      show (SA c A 𝒱).cechDiff (E.pairMap x) = E.e01 _
      rw [pairMap_apply, ← e01_cechDiff_baseChange]
    · rintro y ⟨p, rfl⟩
      obtain ⟨x, rfl⟩ := E.pairMap_bijective.2 p
      refine ⟨((𝒱.structureSheafSections c).cechDiff.baseChange A) x, LinearMap.mem_range_self _ _, ?_⟩
      show E.e01 _ = (SA c A 𝒱).cechDiff (E.pairMap x)
      rw [pairMap_apply, e01_cechDiff_baseChange])

end BaseChangeIsos

end Cech

end CechBaseChange

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry TensorProduct"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (e0 : (A ⊗[R] (𝒱.cover c).A0) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A0)
      (e1 : (A ⊗[R] (𝒱.cover c).A1) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A1)
      (e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
      (eH0 : LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A) ≃ₗ[A]
          ((𝒱.pullback c A).structureSheafSections
            (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H0)
      (eH1 : ((A ⊗[R] (𝒱.cover c).A01) ⧸ LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange A))
          ≃ₗ[A] ((𝒱.pullback c A).structureSheafSections
            (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
      (∀ s, e0 ((1 : A) ⊗ₜ[R] s) = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app 𝒱.U0).hom s) ∧
      (∀ s, e1 ((1 : A) ⊗ₜ[R] s) = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app 𝒱.U1).hom s) ∧
      (∀ s, e01 ((1 : A) ⊗ₜ[R] s)
          = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) ∧
      (∀ x, ((eH0 x : _ × _)) = (e0 (TensorProduct.prodRight R A A _ _ x.1).1,
          e1 (TensorProduct.prodRight R A A _ _ x.1).2)) ∧
      (∀ y, eH1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 y)) := by
  obtain ⟨e0, he0⟩ := exists_algEquiv_sections_baseChange c 𝒱.U0 𝒱.isAffineOpen_U0 A
  obtain ⟨e1, he1⟩ := exists_algEquiv_sections_baseChange c 𝒱.U1 𝒱.isAffineOpen_U1 A
  obtain ⟨e01, he01⟩ := exists_algEquiv_sections_baseChange c (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf A
  let E : CechBaseChange.BaseChangeIsos c A 𝒱 :=
    { e0 := e0, e1 := e1, e01 := e01, he0 := he0, he1 := he1, he01 := he01 }
  exact ⟨e0, e1, e01, E.kerEquivH0, E.cokerEquivH1, he0, he1, he01, fun x => rfl, fun y => rfl⟩

end

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf (solution)
