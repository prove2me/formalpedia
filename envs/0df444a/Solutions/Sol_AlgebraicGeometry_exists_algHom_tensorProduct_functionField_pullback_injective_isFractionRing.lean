-- Prove2me | solution 1 for AlgebraicGeometry.exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7fc60203-add8-5eab-b8c1-71bd70b7de11

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.AlgebraicGeometry AlgebraicCurve Topology TopologicalSpace"
open scoped TensorProduct

set_option autoImplicit false

open scoped TensorProduct nonZeroDivisors

namespace Algebra
p2m_export "Algebra" "ofId map_top TensorProduct.includeRight TensorProduct.lift_tmul algebraMap TensorProduct.lift TensorProduct.map_tmul algebraMapSubmonoid TensorProduct.includeLeft_injective TensorProduct.comm TensorProduct.algebraMap_apply algebraMap_self smul_def TensorProduct.includeLeft id TensorProduct.comm_tmul TensorProduct.isField_of_isAlgebraic TensorProduct.map commutes' TensorProduct.includeLeftRingHom"
namespace TensorProduct
p2m_export "Algebra.TensorProduct" "includeRight lift_tmul congr lift map_tmul includeLeft_injective algebraMap_apply includeLeft map_comp comm_tmul isField_of_isAlgebraic map ext includeLeftRingHom"
p2m_open "Algebra.TensorProduct Algebra"

section RingLeft

variable (K L A FA : Type*) [Field K] [Field L] [Algebra K L]
  [CommRing A] [Algebra K A] [CommRing FA] [Algebra A FA] [Algebra K FA] [IsScalarTower K A FA]

noncomputable def fracMapRight : A ⊗[K] L →ₐ[K] FA ⊗[K] L :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A FA) (AlgHom.id K L)

@[scoped simp]
theorem fracMapRight_tmul (a : A) (l : L) :
    fracMapRight K L A FA (a ⊗ₜ l) = algebraMap A FA a ⊗ₜ l := rfl

@[reducible] noncomputable def fracAlgebraRight : Algebra (A ⊗[K] L) (FA ⊗[K] L) :=
  (fracMapRight K L A FA).toRingHom.toAlgebra

theorem isScalarTower_fracAlgebraRight :
    letI : Algebra (A ⊗[K] L) (FA ⊗[K] L) := fracAlgebraRight K L A FA
    IsScalarTower A (A ⊗[K] L) (FA ⊗[K] L) := by
  letI : Algebra (A ⊗[K] L) (FA ⊗[K] L) := fracAlgebraRight K L A FA
  show IsScalarTower A (A ⊗[K] L) (FA ⊗[K] L)
  refine IsScalarTower.of_algebraMap_eq (R := A) (S := A ⊗[K] L) (A := FA ⊗[K] L) fun a => ?_
  show algebraMap A (FA ⊗[K] L) a = fracMapRight K L A FA (algebraMap A (A ⊗[K] L) a)
  rw [Algebra.TensorProduct.algebraMap_apply (R := K) (S := A) (A := A) (B := L),
    Algebra.TensorProduct.algebraMap_apply (R := K) (S := A) (A := FA) (B := L),
    Algebra.algebraMap_self, RingHom.id_apply, fracMapRight_tmul]

theorem isLocalization_fracAlgebraRight [IsFractionRing A FA] :
    letI : Algebra (A ⊗[K] L) (FA ⊗[K] L) := fracAlgebraRight K L A FA
    IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[K] L) (A⁰)) (FA ⊗[K] L) := by
  letI : Algebra (A ⊗[K] L) (FA ⊗[K] L) := fracAlgebraRight K L A FA
  haveI : IsScalarTower A (A ⊗[K] L) (FA ⊗[K] L) := isScalarTower_fracAlgebraRight K L A FA
  show IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[K] L) (A⁰)) (FA ⊗[K] L)
  refine IsLocalization.tensorProduct_tensorProduct K L (A⁰) FA ?_
  ext l
  show fracMapRight K L A FA ((1 : A) ⊗ₜ l) = (1 : FA) ⊗ₜ l
  rw [fracMapRight_tmul, map_one]

theorem algebraMapSubmonoid_le_nonZeroDivisors [Nontrivial A] [IsDomain (A ⊗[K] L)] :
    Algebra.algebraMapSubmonoid (A ⊗[K] L) (A⁰) ≤ (A ⊗[K] L)⁰ := by
  rintro _ ⟨a, ha, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L) :=
    Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K L).injective
  exact nonZeroDivisors.ne_zero ha (hinj (by rw [map_zero]; exact h))

variable (F : Type*) [CommRing F] [Algebra (A ⊗[K] L) F]
variable [IsDomain A] [IsFractionRing A FA] [IsDomain (A ⊗[K] L)] [IsFractionRing (A ⊗[K] L) F]

noncomputable def fracLiftRight : FA ⊗[K] L →+* F :=
  letI : Algebra (A ⊗[K] L) (FA ⊗[K] L) := fracAlgebraRight K L A FA
  haveI := isLocalization_fracAlgebraRight K L A FA
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid (A ⊗[K] L) (A⁰)) (S := FA ⊗[K] L)
    (g := algebraMap (A ⊗[K] L) F)
    (fun m => IsLocalization.map_units F ⟨m.1, algebraMapSubmonoid_le_nonZeroDivisors K L A m.2⟩)

theorem fracLiftRight_fracMapRight (x : A ⊗[K] L) :
    fracLiftRight K L A FA F (fracMapRight K L A FA x) = algebraMap (A ⊗[K] L) F x := by
  letI : Algebra (A ⊗[K] L) (FA ⊗[K] L) := fracAlgebraRight K L A FA
  haveI := isLocalization_fracAlgebraRight K L A FA
  exact IsLocalization.lift_eq _ x

@[scoped simp]
theorem fracLiftRight_tmul (a : A) (l : L) :
    fracLiftRight K L A FA F (algebraMap A FA a ⊗ₜ l) = algebraMap (A ⊗[K] L) F (a ⊗ₜ l) := by
  rw [← fracMapRight_tmul, fracLiftRight_fracMapRight]

theorem isFractionRing_fracLiftRight :
    letI : Algebra (FA ⊗[K] L) F := (fracLiftRight K L A FA F).toAlgebra
    IsFractionRing (FA ⊗[K] L) F := by
  letI : Algebra (A ⊗[K] L) (FA ⊗[K] L) := fracAlgebraRight K L A FA
  haveI := isLocalization_fracAlgebraRight K L A FA
  letI : Algebra (FA ⊗[K] L) F := (fracLiftRight K L A FA F).toAlgebra
  show IsFractionRing (FA ⊗[K] L) F
  haveI : IsScalarTower (A ⊗[K] L) (FA ⊗[K] L) F :=
    IsScalarTower.of_algebraMap_eq (R := A ⊗[K] L) (S := FA ⊗[K] L) (A := F) fun x =>
      (fracLiftRight_fracMapRight K L A FA F x).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid (A ⊗[K] L) (A⁰)) (FA ⊗[K] L) F

end RingLeft

section RingLeftField

variable (K L A FA : Type*) [Field K] [Field L] [Algebra K L]
  [CommRing A] [Algebra K A] [CommRing FA] [Algebra A FA] [Algebra K FA] [IsScalarTower K A FA]
  (F : Type*) [Field F] [Algebra (A ⊗[K] L) F]
  [IsDomain A] [IsFractionRing A FA] [IsDomain (A ⊗[K] L)] [IsFractionRing (A ⊗[K] L) F]

theorem fracLiftRight_bijective (hF : IsField (FA ⊗[K] L)) :
    Function.Bijective (fracLiftRight K L A FA F) := by
  letI : Algebra (FA ⊗[K] L) F := (fracLiftRight K L A FA F).toAlgebra
  haveI : IsFractionRing (FA ⊗[K] L) F := isFractionRing_fracLiftRight K L A FA F
  letI : Field (FA ⊗[K] L) := hF.toField
  refine ⟨IsFractionRing.injective (FA ⊗[K] L) F, fun y => ?_⟩
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := FA ⊗[K] L) y
  refine ⟨n * d⁻¹, ?_⟩
  show algebraMap (FA ⊗[K] L) F (n * d⁻¹) = algebraMap _ F n / algebraMap _ F d
  rw [map_mul, map_inv₀, div_eq_mul_inv]

end RingLeftField

section Domain

variable (K L A FA : Type*) [Field K] [Field L] [Algebra K L]
  [CommRing A] [IsDomain A] [Algebra K A]
  [CommRing FA] [Algebra A FA] [Algebra K FA] [IsScalarTower K A FA] [IsFractionRing A FA]

theorem isDomain_fractionRing_tensorProduct_of_isDomain [IsDomain (A ⊗[K] L)] : IsDomain (FA ⊗[K] L) := by
  letI : Algebra (A ⊗[K] L) (FA ⊗[K] L) := fracAlgebraRight K L A FA
  haveI := isLocalization_fracAlgebraRight K L A FA
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (FA ⊗[K] L) (algebraMapSubmonoid_le_nonZeroDivisors K L A)

theorem isDomain_tensorProduct_fractionRing_of_isDomain [IsDomain (L ⊗[K] A)] : IsDomain (L ⊗[K] FA) := by
  haveI : IsDomain (A ⊗[K] L) :=
    MulEquiv.isDomain (L ⊗[K] A) (Algebra.TensorProduct.comm K A L).toMulEquiv
  haveI : IsDomain (FA ⊗[K] L) := isDomain_fractionRing_tensorProduct_of_isDomain K L A FA
  exact MulEquiv.isDomain (FA ⊗[K] L) (Algebra.TensorProduct.comm K L FA).toMulEquiv

theorem isField_tensorProduct_fractionRing_of_isDomain [Algebra.IsAlgebraic K L] [IsDomain (L ⊗[K] A)]
    [hFA : Fact (IsField FA)] : IsField (L ⊗[K] FA) := by
  letI : Field FA := hFA.out.toField
  haveI := isDomain_tensorProduct_fractionRing_of_isDomain K L A FA
  exact Algebra.TensorProduct.isField_of_isAlgebraic K L FA (Or.inl inferInstance)

end Domain

end Algebra.TensorProduct
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra.TensorProduct"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra"

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Scheme.Hom Scheme.Γ Scheme.Hom.germ_stalkMap_apply IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec IsIntegral Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.Hom.appTop Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc functionField_isFractionRing_of_isAffineOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst isAffineOpen_top IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.generalizingMap IsAffineHom Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.isAffineHom_fst"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Opens.topIso_inv germToFunctionField Hom Γ Hom.germ_stalkMap_apply topIso_hom topIso ΓSpecIso_inv_naturality Hom.appTop isoSpec_Spec_inv functionField Opens.topIso_hom Hom.comp_appTop isoSpec isBasis_affineOpens Opens Hom.appLE_map Hom.app_eq_appLE Opens.ι_appTop Hom.appLE ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom TwoAffineOpenCover.isAffineHom_fst"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom algebraMap_algebraOfHom isAffineHom_fst pullback"
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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra.TensorProduct"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra.TensorProduct"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra.TensorProduct"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra.TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Scheme.Hom Scheme.Γ Scheme.Hom.germ_stalkMap_apply IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec IsIntegral Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.Hom.appTop Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc functionField_isFractionRing_of_isAffineOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst isAffineOpen_top IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.generalizingMap IsAffineHom Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.isAffineHom_fst"
p2m_open "AlgebraicGeometry"

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover _root_.P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.AlgebraicGeometry.Scheme.TwoAffineOpenCover in

theorem exists_algEquiv_tensorProduct_sections_preimage
    {K : Type u} [Field K] (K' : Type u) [Field K'] [Algebra K K']
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty (U : Scheme.{u})] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom x U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
      ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U)
    ∃ e : K' ⊗[K] Γ(X, U) ≃ₐ[K']
        Γ(pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K'))),
          (pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U),
      ∀ s : Γ(X, U), e (1 ⊗ₜ s) = ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).app U).hom s :=
  exists_algEquiv_sections_baseChange x U hU K'

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra.TensorProduct"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra.TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Scheme.Hom Scheme.Γ Scheme.Hom.germ_stalkMap_apply IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec IsIntegral Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.Hom.appTop Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc functionField_isFractionRing_of_isAffineOpen Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst isAffineOpen_top IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.generalizingMap IsAffineHom Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.isAffineHom_fst"
p2m_open "AlgebraicGeometry"

theorem base_genericPoint_eq_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f (genericPoint X) = genericPoint Y := by
  have hgen := Flat.generalizingMap f
  have hsp : genericPoint Y ⤳ f (genericPoint X) := genericPoint_specializes _
  obtain ⟨x', hx', hfx'⟩ := hgen hsp
  have hx'' : genericPoint X ⤳ x' := genericPoint_specializes _
  have heq : x' = genericPoint X := (hx'.antisymm hx'').eq
  rw [← hfx', heq]

theorem pullback_fst_base_genericPoint_of_field
    {K : Type u} [Field K] (K' : Type u) [Field K'] [Algebra K K']
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [IsIntegral ↑(pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))] :
    (pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).base
        (genericPoint ↑(pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) =
      genericPoint X :=
  base_genericPoint_eq_of_flat _

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Opens.topIso_inv germToFunctionField Hom Γ Hom.germ_stalkMap_apply topIso_hom topIso ΓSpecIso_inv_naturality Hom.appTop isoSpec_Spec_inv functionField Opens.topIso_hom Hom.comp_appTop isoSpec isBasis_affineOpens Opens Hom.appLE_map Hom.app_eq_appLE Opens.ι_appTop Hom.appLE ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom TwoAffineOpenCover.isAffineHom_fst" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "map_appLE image germ_stalkMap_apply app injective stalkMap appTop comp_appTop appLE_map app_eq_appLE comp_apply appLE" end Scheme.Hom
namespace Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.functionFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsIntegral X] [IsIntegral Y] : Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq (base_genericPoint_eq_of_flat f).symm)).hom ≫
    f.stalkMap (genericPoint X)

end Scheme.Hom
p2m_export "AlgebraicGeometry" "Scheme.Hom.functionFieldMap"
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.functionFieldMap_germToFunctionField {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsIntegral X] [IsIntegral Y] (U : Y.Opens) [Nonempty (U : Scheme.{u})]
    [Nonempty ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u})] (s : Γ(Y, U)) :
    f.functionFieldMap (Y.germToFunctionField U s) = X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
  have hη : f (genericPoint X) = genericPoint Y := base_genericPoint_eq_of_flat f
  have hmem : f (genericPoint X) ∈ U := by
    rw [hη]; exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty (U : Scheme.{u})))
  show (f.stalkMap (genericPoint X)).hom
      ((Y.presheaf.stalkCongr (.of_eq hη.symm)).hom.hom (Y.presheaf.germ U (genericPoint Y) _ s)) =
    X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) _ (f.app U s)
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

theorem isScalarTower_sections_functionField {R : Type u} [Field R] {X : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) [Nonempty (U : Scheme.{u})] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    IsScalarTower R Γ(X, U) X.functionField := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) =
    (X.presheaf.germ U (genericPoint X) _).hom
      ((c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]
  rfl

section Main

variable {K : Type u} [Field K] (K' : Type u) [Field K'] [Algebra K K']
  {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
  [IsIntegral ↑(pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))]

local notation "X'" => pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))
local notation "π" => pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))
local notation "ϖ" => pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap K K')))

theorem functionFieldMap_comp_baseToFunctionField :
    (Scheme.Hom.functionFieldMap (π)).hom.comp (baseToFunctionField x) =
      (baseToFunctionField (ϖ)).comp (algebraMap K K') := by
  haveI : Nonempty ((⊤ : X.Opens) : Scheme.{u}) := by
    exact ⟨⟨genericPoint X, trivial⟩⟩
  haveI : Nonempty (((π) ⁻¹ᵁ (⊤ : X.Opens) : (X').Opens) : Scheme.{u}) := by
    exact ⟨⟨genericPoint ((X') : Scheme.{u}), trivial⟩⟩
  ext a

  have h1 := Scheme.Hom.functionFieldMap_germToFunctionField (π) ⊤
    (x.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

  have hsq : (π).app ⊤ (x.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
      (ϖ).appTop ((Spec.map (CommRingCat.ofHom (algebraMap K K'))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) := by
    have h := congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))
      (pullback.condition (f := x) (g := Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
    exact h

  have hnat : (Spec.map (CommRingCat.ofHom (algebraMap K K'))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of K')).inv (algebraMap K K' a) := by
    have h := congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K K')))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
    exact h.symm
  show (Scheme.Hom.functionFieldMap (π)).hom
      ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom
        (x.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))) =
    ((X').presheaf.germ ⊤ (genericPoint ((X') : Scheme.{u})) trivial).hom
      ((ϖ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K')).inv.hom (algebraMap K K' a)))
  rw [← hnat, ← hsq]
  exact h1

theorem exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing :
    letI := (baseToFunctionField x).toAlgebra
    letI := (baseToFunctionField (ϖ)).toAlgebra
    ∃ Φ : K' ⊗[K] X.functionField →ₐ[K'] (X').functionField,
      Function.Injective Φ ∧
      (letI := Φ.toRingHom.toAlgebra; IsFractionRing (K' ⊗[K] X.functionField) (X').functionField) ∧
      ∀ (U : X.Opens) [hU : Nonempty (U : Scheme.{u})]
        [hU' : Nonempty (((π) ⁻¹ᵁ U : (X').Opens) : Scheme.{u})]
        (s : Γ(X, U)),
        Φ (1 ⊗ₜ X.germToFunctionField U s) =
          (X').germToFunctionField ((π) ⁻¹ᵁ U) ((π).app U s) := by
  letI := (baseToFunctionField x).toAlgebra
  letI := (baseToFunctionField (ϖ)).toAlgebra
  letI : Algebra K (X').functionField := ((baseToFunctionField (ϖ)).comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower K K' (X').functionField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let πff : X.functionField →ₐ[K] (X').functionField :=
    { (Scheme.Hom.functionFieldMap (π)).hom with
      commutes' := fun a => by
        have h := congrArg (fun φ : K →+* (X').functionField => φ a)
          (functionFieldMap_comp_baseToFunctionField K' x)
        exact h }
  let Φ₀ : K' ⊗[K] X.functionField →ₐ[K'] (X').functionField :=
    Algebra.TensorProduct.lift (Algebra.ofId K' _) πff (fun _ _ => Commute.all _ _)
  have hΦ₀ : ∀ (c : K') (f : X.functionField), Φ₀ (c ⊗ₜ f) = algebraMap K' _ c * πff f := by
    intro c f
    exact Algebra.TensorProduct.lift_tmul _ _ _ c f

  obtain ⟨U, hU, hηU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  haveI hUne : Nonempty (U : Scheme.{u}) := ⟨⟨genericPoint X, hηU⟩⟩
  haveI hVne : Nonempty (((π) ⁻¹ᵁ U : (X').Opens) : Scheme.{u}) :=
    ⟨⟨genericPoint ((X') : Scheme.{u}),
      show (π).base (genericPoint ((X') : Scheme.{u})) ∈ U by
        rw [pullback_fst_base_genericPoint_of_field K' x]; exact hηU⟩⟩
  haveI : IsAffineHom (π) := Scheme.TwoAffineOpenCover.isAffineHom_fst x K'
  have hV : IsAffineOpen ((π) ⁻¹ᵁ U) := hU.preimage _
  letI algU : Algebra K Γ(X, U) := Scheme.TwoAffineOpenCover.algebraOfHom x U
  letI algV : Algebra K' Γ(X', (π) ⁻¹ᵁ U) := Scheme.TwoAffineOpenCover.algebraOfHom (ϖ) ((π) ⁻¹ᵁ U)
  haveI hSTU : IsScalarTower K Γ(X, U) X.functionField := isScalarTower_sections_functionField x U
  haveI hSTV : IsScalarTower K' Γ(X', (π) ⁻¹ᵁ U) (X').functionField :=
    isScalarTower_sections_functionField (ϖ) ((π) ⁻¹ᵁ U)
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  haveI := functionField_isFractionRing_of_isAffineOpen (X') ((π) ⁻¹ᵁ U) hV
  obtain ⟨e, he⟩ := exists_algEquiv_tensorProduct_sections_preimage K' x U hU
  haveI : IsDomain (K' ⊗[K] Γ(X, U)) := MulEquiv.isDomain _ e.toMulEquiv

  let γ : Γ(X, U) →ₐ[K] X.functionField := IsScalarTower.toAlgHom K Γ(X, U) X.functionField
  have key : ∀ t : K' ⊗[K] Γ(X, U),
      algebraMap Γ(X', (π) ⁻¹ᵁ U) (X').functionField (e t) =
        Φ₀ (Algebra.TensorProduct.map (AlgHom.id K' K') γ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [map_add, ha, hb]
    | tmul c s =>
      have hcs : (c ⊗ₜ[K] s : K' ⊗[K] Γ(X, U)) = c • ((1 : K') ⊗ₜ[K] s) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hcs, map_smul, he s, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        map_smul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_smul, hΦ₀, map_one, one_mul,
        Algebra.smul_def]
      congr 1
      exact (Scheme.Hom.functionFieldMap_germToFunctionField (π) U s).symm

  letI algT : Algebra (K' ⊗[K] Γ(X, U)) (K' ⊗[K] X.functionField) :=
    (Algebra.TensorProduct.map (AlgHom.id K' K') γ).toRingHom.toAlgebra
  haveI : IsScalarTower K' (K' ⊗[K] Γ(X, U)) (K' ⊗[K] X.functionField) :=
    IsScalarTower.of_algebraMap_eq (R := K') (S := K' ⊗[K] Γ(X, U)) (A := K' ⊗[K] X.functionField) (fun c => by
      rw [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      change c ⊗ₜ[K] (1 : X.functionField) = Algebra.TensorProduct.map (AlgHom.id K' K') γ (c ⊗ₜ[K] (1 : Γ(X, U)))
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply])
  haveI hloc : IsLocalization ((nonZeroDivisors Γ(X, U)).map
      (Algebra.TensorProduct.includeRight (R := K) (A := K'))) (K' ⊗[K] X.functionField) :=
    IsLocalization.tensorProduct_tensorProduct_right K K' (nonZeroDivisors Γ(X, U)) X.functionField
      (by ext s; simp [RingHom.algebraMap_toAlgebra]; rfl)

  letI algL : Algebra (K' ⊗[K] Γ(X, U)) (X').functionField :=
    ((algebraMap Γ(X', (π) ⁻¹ᵁ U) (X').functionField).comp e.toRingEquiv.toRingHom).toAlgebra
  haveI hfracB : IsFractionRing (K' ⊗[K] Γ(X, U)) (X').functionField :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (R := Γ(X', (π) ⁻¹ᵁ U)) (S := (X').functionField)
      e.toRingEquiv.symm).mp inferInstance

  letI algΦ : Algebra (K' ⊗[K] X.functionField) (X').functionField := Φ₀.toRingHom.toAlgebra
  haveI : IsScalarTower (K' ⊗[K] Γ(X, U)) (K' ⊗[K] X.functionField) (X').functionField :=
    IsScalarTower.of_algebraMap_eq (fun t => key t)
  have hfrac : IsFractionRing (K' ⊗[K] X.functionField) (X').functionField :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      ((nonZeroDivisors Γ(X, U)).map (Algebra.TensorProduct.includeRight (R := K) (A := K')))
      (K' ⊗[K] X.functionField) (X').functionField
  have hinj : Function.Injective Φ₀ := IsFractionRing.injective (K' ⊗[K] X.functionField) (X').functionField
  refine ⟨Φ₀, hinj, hfrac, ?_⟩
  intro U hU hU' s
  rw [hΦ₀, map_one, one_mul]
  exact Scheme.Hom.functionFieldMap_germToFunctionField (π) U s

end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra.TensorProduct"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing.Algebra.TensorProduct"

theorem solution
    {K : Type u} [Field K] (K' : Type u) [Field K'] [Algebra K K']
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [IsIntegral ↑(pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))] :
    letI := (baseToFunctionField x).toAlgebra
    letI := (baseToFunctionField
      (pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))).toAlgebra
    ∃ Φ : K' ⊗[K] X.functionField →ₐ[K']
        (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField,
      Function.Injective Φ ∧
      (letI := Φ.toRingHom.toAlgebra
       IsFractionRing (K' ⊗[K] X.functionField)
         (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).functionField) ∧
      ∀ (U : X.Opens) [hU : Nonempty (U : Scheme.{u})]
        [hU' : Nonempty (((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U : (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).Opens) : Scheme.{u})]
        (s : Γ(X, U)),
        Φ (1 ⊗ₜ X.germToFunctionField U s) =
          (pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).germToFunctionField
            ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U)
            ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).app U s) := by
  exact AlgebraicGeometry.exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing K' x

end S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing
end P2MW
export P2MW.S_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing (solution)
