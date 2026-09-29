-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d1402719-169e-52b2-8cd7-44105b36452e

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq.AlgebraicGeometry"
open scoped TensorProduct

universe u v w

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.fromSpecResidueField Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Surjective Scheme.Hom Scheme.Γ Scheme.Hom.germ_stalkMap_apply pointOfClosedPoint IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Scheme.Opens.toScheme Scheme.Hom.stalkMap_comp Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Opens.topIso_hom SpecMap_residueFieldIsoBase_inv Scheme.Hom.comp_appTop Spec.map_injective pointEquivClosedPoint pointOfClosedPoint_comp pullbackSpecIso_inv_fst Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField SpecMap_ΓSpecIso_hom isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Spec.map_id IsOpenImmersion.iff_isIso_stalkMap IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.fromSpecStalk_toSpecΓ_assoc Scheme.Hom.germ_stalkMap IsAffineHom Scheme.Opens.ι_appTop toSpecΓ residueFieldIsoBase Scheme.Hom.comp_apply Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE fromSpecResidueField Opens.topIso_inv germToFunctionField fromSpecStalk Hom mk Γ Hom.germ_stalkMap_apply topIso_hom topIso Opens.toScheme Hom.stalkMap_comp toSpecΓ_naturality ΓSpecIso_inv_naturality isoSpec_Spec_inv functionField stalkClosedPointTo Opens.topIso_hom Hom.comp_appTop isoSpec descResidueField_stalkClosedPointTo_fromSpecResidueField descResidueField Opens residue Hom.appLE_map Hom.app_eq_appLE fromSpecStalk_toSpecΓ_assoc Hom.germ_stalkMap Opens.ι_appTop Hom.comp_apply Hom.appLE ΓSpecIso toSpecΓ Hom.appLE_eq_app TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom"
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

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.fromSpecResidueField Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Surjective Scheme.Hom Scheme.Γ Scheme.Hom.germ_stalkMap_apply pointOfClosedPoint IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Scheme.Opens.toScheme Scheme.Hom.stalkMap_comp Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Opens.topIso_hom SpecMap_residueFieldIsoBase_inv Scheme.Hom.comp_appTop Spec.map_injective pointEquivClosedPoint pointOfClosedPoint_comp pullbackSpecIso_inv_fst Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField SpecMap_ΓSpecIso_hom isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Spec.map_id IsOpenImmersion.iff_isIso_stalkMap IsAffineOpen pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.fromSpecStalk_toSpecΓ_assoc Scheme.Hom.germ_stalkMap IsAffineHom Scheme.Opens.ι_appTop toSpecΓ residueFieldIsoBase Scheme.Hom.comp_apply Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
p2m_open "AlgebraicGeometry"

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover _root_.P2MW.S_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq.AlgebraicGeometry.Scheme.TwoAffineOpenCover in

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

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq.AlgebraicGeometry AlgebraicCurve"

namespace ConstExt

open scoped TensorProduct

theorem eq_map_of_le
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    (B : Type*) [CommRing B] [Algebra κ B] (𝔫 : Ideal B)
    (hκ : ∀ b : B, ∃ c : κ, b - algebraMap κ B c ∈ 𝔫)
    (P : Ideal (k ⊗[κ] B)) (hP : P ≠ ⊤)
    (hle : Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[κ] k ⊗[κ] B) 𝔫 ≤ P) :
    P = Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[κ] k ⊗[κ] B) 𝔫 := by
  classical
  set J := Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[κ] k ⊗[κ] B) 𝔫 with hJ
  let f : k →+* (k ⊗[κ] B) ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap k (k ⊗[κ] B))
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [f]⟩
    | tmul a b =>
      obtain ⟨c, hb⟩ := hκ b
      refine ⟨c • a, ?_⟩
      show Ideal.Quotient.mk J (algebraMap k (k ⊗[κ] B) (c • a)) = Ideal.Quotient.mk J (a ⊗ₜ[κ] b)
      rw [Ideal.Quotient.eq]
      have hmem : a ⊗ₜ[κ] (b - algebraMap κ B c) ∈ J := by
        have := Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight : B →ₐ[κ] k ⊗[κ] B) hb
        have hmul : a ⊗ₜ[κ] (b - algebraMap κ B c) =
            (a ⊗ₜ[κ] (1 : B)) * ((Algebra.TensorProduct.includeRight : B →ₐ[κ] k ⊗[κ] B) (b - algebraMap κ B c)) := by
          rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [hmul]
        exact Ideal.mul_mem_left _ _ this
      have hcalc : algebraMap k (k ⊗[κ] B) (c • a) - a ⊗ₜ[κ] b = -(a ⊗ₜ[κ] (b - algebraMap κ B c)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, TensorProduct.tmul_sub,
          neg_sub]
        congr 1
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [hcalc]
      exact J.neg_mem hmem
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  have hJtop : J ≠ ⊤ := fun h => hP (top_le_iff.mp (h ▸ hle))
  have hJmax : J.IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    have hker : RingHom.ker f = ⊥ := by
      rcases Ideal.eq_bot_or_top (RingHom.ker f) with h | h
      · exact h
      · exfalso
        apply hJtop
        have h1 : f 1 = 0 := by rw [← RingHom.mem_ker, h]; trivial
        rw [map_one] at h1
        exact Ideal.Quotient.zero_eq_one_iff.mp h1.symm
    have hinj : Function.Injective f := (RingHom.injective_iff_ker_eq_bot f).mpr hker
    exact (RingEquiv.ofBijective f ⟨hinj, hf⟩).symm.toMulEquiv.isField (Field.toIsField k)
  exact (hJmax.eq_of_le hP hle).symm

end ConstExt

theorem solution
    {κ : Type u} [Field κ] [IsAlgClosed κ] {k : Type u} [Field k] [IsAlgClosed k] (φ : κ →+* k)
    {F₀ : Type v} [Field F₀] [Algebra κ F₀] {F : Type w} [Field F] [Algebra k F]
    (M₀ : CurveModel κ F₀) (M : CurveModel k F)
    (e : M.C ≅ pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ)))
    (he : e.hom ≫ pullback.snd M₀.toBase (Spec.map (CommRingCat.ofHom φ)) = M.toBase)
    (ψ : F₀ →+* F)

    (hsq : ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U))] (s : Γ(M₀.C, U)),
      M.ffEquiv.symm (M.C.germToFunctionField ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom s)) =
        ψ (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s))) :

    (∀ y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}, ∃! y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1) ∧

    (∀ (y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}) (y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1 →
      (M.pointEquivPlace y).toValuationSubring.comap ψ = (M₀.pointEquivPlace y₀).toValuationSubring ∧
        ∀ f : F₀, (M.pointEquivPlace y).ord (ψ f) = (M₀.pointEquivPlace y₀).ord f) ∧

    (∀ Q : Place k F,
      (∀ (y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}) (y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
        y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1 → Q ≠ M.pointEquivPlace y) →
      ∀ f : F₀, f ≠ 0 → Q.ord (ψ f) = 0) := by
  classical

  have hpr_def : (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) := rfl

  have L3 : ∀ y₀ : {q : Spec (CommRingCat.of κ) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _}, ∃! y : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀.1 := by
    intro y₀

    let ybar : Spec (CommRingCat.of k) ⟶ pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ)) :=
      pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ y₀.1) (𝟙 _)
        (by rw [Category.assoc, y₀.2, Category.comp_id, Category.id_comp])
    refine ⟨⟨ybar ≫ e.inv, ?_⟩, ?_, ?_⟩
    · rw [Category.assoc, ← he, e.inv_hom_id_assoc, pullback.lift_snd]
    · show (ybar ≫ e.inv) ≫ e.hom ≫ pullback.fst _ _ = _
      rw [Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]
    · intro y' hy'
      apply Subtype.ext
      show y'.1 = ybar ≫ e.inv
      rw [← cancel_mono e.hom, Category.assoc, e.inv_hom_id, Category.comp_id]
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        simpa only [Category.assoc] using hy'
      · rw [pullback.lift_snd, Category.assoc, he, y'.2]
  refine ⟨L3, ?_, ?_⟩
  ·
    intro y₀ y hover

    have hbase : (y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))) ≫ M₀.toBase = Spec.map (CommRingCat.ofHom φ) := by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, he, ← Category.assoc, y.2,
        Category.id_comp]
    have hz0 : (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) = y₀.1.base (IsLocalRing.closedPoint κ) := by
      rw [← Scheme.Hom.comp_apply, hover, Scheme.Hom.comp_apply]
      congr 1
      exact Subsingleton.elim _ _
    have hcl0 : IsClosed ({(((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))} : Set M₀.C) := by
      rw [hz0]; exact (pointEquivClosedPoint M₀.toBase y₀).2

    have hQz : ((M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
        (algebraMap (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k))) M.C.functionField)).range =
        (M.pointEquivPlace y).toValuationSubring.toSubring := by
      rw [CurveModel.pointEquivPlace_apply]
      exact M.range_stalk_eq (pointEquivClosedPoint M.toBase y)
    have hQz₀ : ((M₀.ffEquiv.symm : M₀.C.functionField ≃+* F₀).toRingHom.comp
        (algebraMap (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) M₀.C.functionField)).range =
        (M₀.pointEquivPlace y₀).toValuationSubring.toSubring := by
      rw [CurveModel.pointEquivPlace_apply]
      have hpt : pointEquivClosedPoint M₀.toBase y₀ = ⟨(((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))), hcl0⟩ := Subtype.ext hz0.symm
      rw [hpt]
      exact M₀.range_stalk_eq ⟨_, hcl0⟩

    have hC : ∀ t : M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))),
        ψ (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t)) =
          M.ffEquiv.symm (algebraMap _ M.C.functionField ((((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).stalkMap (y.1.base (IsLocalRing.closedPoint k))).hom t)) := by
      intro t
      obtain ⟨U, hzU, s, rfl⟩ := TopCat.Presheaf.germ_exist M₀.C.presheaf (x := (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) t
      haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hzU⟩⟩
      have hzU' : (y.1.base (IsLocalRing.closedPoint k)) ∈ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U := hzU
      haveI : Nonempty (Scheme.Opens.toScheme ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U)) := ⟨⟨_, hzU'⟩⟩
      have h1 : algebraMap _ M₀.C.functionField ((M₀.C.presheaf.germ U _ hzU).hom s) = M₀.C.germToFunctionField U s := by
        show (M₀.C.presheaf.germ U _ hzU ≫ M₀.C.presheaf.stalkSpecializes _).hom s = _
        rw [TopCat.Presheaf.germ_stalkSpecializes]
      rw [h1, ← hsq U s, Scheme.Hom.germ_stalkMap_apply]
      congr 1
      show _ = (M.C.presheaf.germ _ _ hzU' ≫ M.C.presheaf.stalkSpecializes _).hom _
      rw [TopCat.Presheaf.germ_stalkSpecializes]

    have hsub : ∀ x : F₀, x ∈ (M₀.pointEquivPlace y₀).toValuationSubring → ψ x ∈ (M.pointEquivPlace y).toValuationSubring := by
      intro x hx
      have hx' : x ∈ (M₀.pointEquivPlace y₀).toValuationSubring.toSubring := hx
      rw [← hQz₀] at hx'
      obtain ⟨t, rfl⟩ := hx'
      have : ψ (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t)) ∈ (M.pointEquivPlace y).toValuationSubring.toSubring := by
        rw [← hQz, hC t]
        exact ⟨_, rfl⟩
      exact this

    have hRinj : Function.Injective (fun u : M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k)) =>
        M.ffEquiv.symm (algebraMap _ M.C.functionField u)) := fun u u' h =>
      IsFractionRing.injective (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k))) M.C.functionField (M.ffEquiv.symm.injective h)
    have hRnu : ∀ u : M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k)), ¬ IsUnit u →
        M.ffEquiv.symm (algebraMap _ M.C.functionField u) ∈ (M.pointEquivPlace y).toValuationSubring.nonunits := by
      intro u hu
      have humem : M.ffEquiv.symm (algebraMap _ M.C.functionField u) ∈ (M.pointEquivPlace y).toValuationSubring := by
        show _ ∈ (M.pointEquivPlace y).toValuationSubring.toSubring
        rw [← hQz]; exact ⟨u, rfl⟩
      rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      refine ⟨humem, ?_⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      apply hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hunit
      have hwmem : (w : F) ∈ (M.pointEquivPlace y).toValuationSubring.toSubring := w.2
      rw [← hQz] at hwmem
      obtain ⟨u', hu'⟩ := hwmem
      refine isUnit_iff_exists_inv.mpr ⟨u', hRinj ?_⟩
      have h := congrArg Subtype.val hw
      show M.ffEquiv.symm (algebraMap _ M.C.functionField (u * u')) = M.ffEquiv.symm (algebraMap _ M.C.functionField 1)
      rw [map_mul, map_mul, map_one, map_one]
      have hu'' : M.ffEquiv.symm (algebraMap _ M.C.functionField u') = (w : F) := hu'
      rw [hu'']
      exact h

    have hnu : ∀ x : F₀, x ∈ (M₀.pointEquivPlace y₀).toValuationSubring.nonunits →
        ψ x ∈ (M.pointEquivPlace y).toValuationSubring.nonunits := by
      intro x hx
      obtain ⟨hxA, hxm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
      have hx' : x ∈ (M₀.pointEquivPlace y₀).toValuationSubring.toSubring := hxA
      rw [← hQz₀] at hx'
      obtain ⟨t, ht⟩ := hx'
      have htx : M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t) = x := ht

      have htu : ¬ IsUnit t := by
        intro hu
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxm
        apply hxm
        obtain ⟨t', ht'⟩ := isUnit_iff_exists_inv.mp hu
        have ht'mem : M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t') ∈ (M₀.pointEquivPlace y₀).toValuationSubring := by
          show _ ∈ (M₀.pointEquivPlace y₀).toValuationSubring.toSubring
          rw [← hQz₀]; exact ⟨t', rfl⟩
        refine isUnit_iff_exists_inv.mpr ⟨⟨_, ht'mem⟩, Subtype.ext ?_⟩
        show x * M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t') = 1
        rw [← htx, ← map_mul, ← map_mul, ht', map_one, map_one]

      have hsu : ¬ IsUnit ((((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).stalkMap (y.1.base (IsLocalRing.closedPoint k))).hom t) := fun hu =>
        htu ((isUnit_map_iff (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).stalkMap (y.1.base (IsLocalRing.closedPoint k))).hom t).mp hu)
      rw [← htx, hC t]
      exact hRnu _ hsu
    refine ⟨?_, ?_⟩
    ·
      ext x
      constructor
      · intro hx
        change ψ x ∈ (M.pointEquivPlace y).toValuationSubring at hx
        by_contra hx0
        have hxne : x ≠ 0 := by rintro rfl; exact hx0 (zero_mem _)
        have hxi : x⁻¹ ∈ (M₀.pointEquivPlace y₀).toValuationSubring :=
          ((M₀.pointEquivPlace y₀).toValuationSubring.mem_or_inv_mem x).resolve_left hx0
        have hxi_nu : x⁻¹ ∈ (M₀.pointEquivPlace y₀).toValuationSubring.nonunits := by
          rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
          refine ⟨hxi, ?_⟩
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hu
          obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu

          have : (w : F₀) = x := by
            have h : x⁻¹ * (w : F₀) = 1 := congrArg Subtype.val hw
            exact ((inv_mul_eq_one₀ hxne).mp h).symm
          exact hx0 (this ▸ w.2)
        have h1 := hnu _ hxi_nu

        rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at h1
        obtain ⟨hmem1, hmax1⟩ := h1
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax1
        apply hmax1
        refine isUnit_iff_exists_inv.mpr ⟨⟨ψ x, hx⟩, Subtype.ext ?_⟩
        show ψ x⁻¹ * ψ x = 1
        rw [← map_mul, inv_mul_cancel₀ hxne, map_one]
      · intro hx
        exact hsub x hx
    ·
      classical

      obtain ⟨U, hU, hUz⟩ := M₀.finset_subset_affineOpen {(((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))}
      have hzU : (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) ∈ U := hUz _ (Finset.mem_singleton_self _)
      letI instAlg : Algebra κ k := φ.toAlgebra
      letI algU : Algebra κ Γ(M₀.C, U) := Scheme.TwoAffineOpenCover.algebraOfHom M₀.toBase U
      haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hzU⟩⟩
      letI algW := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap κ k))))
        ((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap κ k)))) ⁻¹ᵁ U)
      obtain ⟨eU, heU⟩ := AlgebraicGeometry.exists_algEquiv_tensorProduct_sections_preimage k M₀.toBase U hU
      have heU' : ∀ s : Γ(M₀.C, U), eU (1 ⊗ₜ[κ] s) = ((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom s := heU
      have hfz : (pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).base (e.hom.base (y.1.base (IsLocalRing.closedPoint k))) = (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) := rfl
      have hzW : (e.hom.base (y.1.base (IsLocalRing.closedPoint k))) ∈ (pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U := hzU
      haveI : IsAffineHom (pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) := MorphismProperty.pullback_fst _ _ inferInstance
      have hW : IsAffineOpen ((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) := hU.preimage _

      letI algSt0 : Algebra Γ(M₀.C, U) (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) := TopCat.Presheaf.algebra_section_stalk M₀.C.presheaf ⟨_, hzU⟩
      letI algStP : Algebra Γ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))), (pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.stalk (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))) :=
        TopCat.Presheaf.algebra_section_stalk (pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf ⟨_, hzW⟩
      haveI hloc₀ : IsLocalization.AtPrime (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) (hU.primeIdealOf ⟨_, hzU⟩).asIdeal := hU.isLocalization_stalk ⟨_, hzU⟩
      haveI hloc : IsLocalization.AtPrime ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.stalk (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))) (hW.primeIdealOf ⟨_, hzW⟩).asIdeal := hW.isLocalization_stalk ⟨_, hzW⟩
      have hnat : (hW.primeIdealOf ⟨_, hzW⟩).asIdeal.comap ((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom =
          (hU.primeIdealOf ⟨_, hzU⟩).asIdeal := by
        have h := IsAffineOpen.comap_primeIdealOf_appLE (f := (pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))) (x := (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))) U hU
          ((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) hW le_rfl hzW
        rw [Scheme.Hom.appLE_eq_app] at h
        exact congrArg PrimeSpectrum.asIdeal h
      have h𝔫 : (IsLocalRing.maximalIdeal (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))))).comap (algebraMap Γ(M₀.C, U) (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))))) =
          (hU.primeIdealOf ⟨_, hzU⟩).asIdeal :=
        IsLocalization.AtPrime.under_maximalIdeal (S := (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))))) (I := (hU.primeIdealOf ⟨_, hzU⟩).asIdeal)
      have halg0 : ∀ b : Γ(M₀.C, U), algebraMap Γ(M₀.C, U) (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) b = (M₀.C.presheaf.germ U (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) hzU).hom b := fun b => rfl

      have hρ : ∀ a : κ, (M₀.C.residue (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))).hom ((M₀.C.presheaf.germ ⊤ (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) trivial).hom
          ((M₀.toBase.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom a))) =
          (residueFieldIsoBase M₀.toBase _ hcl0).inv.hom a := by
        intro a
        have hmor : (residueFieldIsoBase M₀.toBase _ hcl0).inv =
            (Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫ M₀.toBase.appTop ≫
              M₀.C.presheaf.germ ⊤ (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) trivial ≫ M₀.C.residue (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) := by
          apply Spec.map_injective
          rw [SpecMap_residueFieldIsoBase_inv, Spec.map_comp, Spec.map_comp, Spec.map_comp]
          have h3 : M₀.C.fromSpecStalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) ≫ M₀.toBase ≫ (Spec (CommRingCat.of κ)).toSpecΓ =
              Spec.map (M₀.C.presheaf.germ ⊤ (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) trivial) ≫ Spec.map M₀.toBase.appTop := by
            rw [Scheme.toSpecΓ_naturality, Scheme.fromSpecStalk_toSpecΓ_assoc]
          rw [← SpecMap_ΓSpecIso_hom] at h3
          have h4 : M₀.C.fromSpecStalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) ≫ M₀.toBase =
              (Spec.map (M₀.C.presheaf.germ ⊤ (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) trivial) ≫ Spec.map M₀.toBase.appTop) ≫
                Spec.map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv := by
            rw [← h3, Category.assoc, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
          rw [Scheme.fromSpecResidueField, Category.assoc, h4, Category.assoc, Category.assoc, Category.assoc]
        have := congrArg (fun f => f.hom a) hmor
        simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this.symm
      have hκ : ∀ b : Γ(M₀.C, U), ∃ c : κ, b - algebraMap κ Γ(M₀.C, U) c ∈ (hU.primeIdealOf ⟨_, hzU⟩).asIdeal := by
        intro b
        refine ⟨(residueFieldIsoBase M₀.toBase _ hcl0).hom.hom ((M₀.C.residue (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))).hom ((M₀.C.presheaf.germ U (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) hzU).hom b)), ?_⟩
        rw [← h𝔫, Ideal.mem_comap, halg0, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, map_sub]

        have hgc : ∀ c : κ, (M₀.C.presheaf.germ U (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) hzU).hom (algebraMap κ Γ(M₀.C, U) c) =
            (M₀.C.presheaf.germ ⊤ (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) trivial).hom ((M₀.toBase.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom c)) := by
          intro c
          show (M₀.C.presheaf.germ U (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) hzU).hom ((M₀.C.presheaf.map (homOfLE le_top).op).hom ((M₀.toBase.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom c))) = _
          exact TopCat.Presheaf.germ_res_apply M₀.C.presheaf (homOfLE le_top) _ hzU _
        intro hunit
        have hres := IsUnit.map (M₀.C.residue (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))).hom hunit
        rw [map_sub, hgc, hρ] at hres

        have h0 : (M₀.C.residue (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))).hom ((M₀.C.presheaf.germ U (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) hzU).hom b) -
            (residueFieldIsoBase M₀.toBase _ hcl0).inv.hom ((residueFieldIsoBase M₀.toBase _ hcl0).hom.hom
              ((M₀.C.residue (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))).hom ((M₀.C.presheaf.germ U (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) hzU).hom b))) = 0 := by
          have hinv : ∀ r, (residueFieldIsoBase M₀.toBase _ hcl0).inv.hom ((residueFieldIsoBase M₀.toBase _ hcl0).hom.hom r) = r := by
            intro r
            change ((residueFieldIsoBase M₀.toBase _ hcl0).hom ≫ (residueFieldIsoBase M₀.toBase _ hcl0).inv).hom r = r
            rw [Iso.hom_inv_id]
            rfl
          rw [hinv, sub_self]
        rw [h0] at hres
        exact not_isUnit_zero hres

      have hprop : ((hW.primeIdealOf ⟨_, hzW⟩).asIdeal.comap eU.toRingEquiv.toRingHom) ≠ ⊤ :=
        Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _)
      have hle : Ideal.map (Algebra.TensorProduct.includeRight : Γ(M₀.C, U) →ₐ[κ] k ⊗[κ] Γ(M₀.C, U)) (hU.primeIdealOf ⟨_, hzU⟩).asIdeal ≤
          (hW.primeIdealOf ⟨_, hzW⟩).asIdeal.comap eU.toRingEquiv.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro b hb
        rw [Ideal.mem_comap, Ideal.mem_comap]
        show eU ((1 : k) ⊗ₜ[κ] b) ∈ (hW.primeIdealOf ⟨_, hzW⟩).asIdeal
        rw [heU', ← Ideal.mem_comap, hnat]
        exact hb
      have h𝔭 := ConstExt.eq_map_of_le κ k Γ(M₀.C, U) _ hκ _ hprop hle

      have halgP : ∀ t, algebraMap Γ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))), (pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.stalk (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))) t =
          ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.germ ((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) (e.hom.base (y.1.base (IsLocalRing.closedPoint k))) hzW).hom t := fun t => rfl
      have hmaxP : IsLocalRing.maximalIdeal ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.stalk (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))) =
          (hW.primeIdealOf ⟨_, hzW⟩).asIdeal.map (algebraMap Γ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))), (pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.stalk (e.hom.base (y.1.base (IsLocalRing.closedPoint k))))) :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal (hW.primeIdealOf ⟨_, hzW⟩).asIdeal ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.stalk (e.hom.base (y.1.base (IsLocalRing.closedPoint k))))).symm
      have hmax0 : IsLocalRing.maximalIdeal (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) =
          (hU.primeIdealOf ⟨_, hzU⟩).asIdeal.map (algebraMap Γ(M₀.C, U) (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))))) :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨_, hzU⟩).asIdeal (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))))).symm
      have h𝔭' : (hW.primeIdealOf ⟨_, hzW⟩).asIdeal = (hU.primeIdealOf ⟨_, hzU⟩).asIdeal.map ((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom := by
        have h1 : (hW.primeIdealOf ⟨_, hzW⟩).asIdeal = ((hW.primeIdealOf ⟨_, hzW⟩).asIdeal.comap eU.toRingEquiv.toRingHom).map eU.toRingEquiv.toRingHom :=
          (Ideal.map_comap_of_surjective _ eU.surjective _).symm
        rw [h1, h𝔭]
        show Ideal.map eU.toRingEquiv.toRingHom (Ideal.map (Algebra.TensorProduct.includeRight : Γ(M₀.C, U) →ₐ[κ] k ⊗[κ] Γ(M₀.C, U)).toRingHom _) = _
        rw [Ideal.map_map]
        congr 1
        apply RingHom.ext
        intro b
        exact heU' b

      let fsm : (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) →+* ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.stalk (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))) := (((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).stalkMap (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))).hom
      have hfsm : ∀ t, fsm t = (((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).stalkMap (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))).hom t := fun t => rfl
      haveI : IsLocalHom fsm := inferInstanceAs (IsLocalHom (((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).stalkMap (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))).hom)
      have hgsm : fsm.comp (M₀.C.presheaf.germ U (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) hzU).hom =
          ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.germ ((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) (e.hom.base (y.1.base (IsLocalRing.closedPoint k))) hzW).hom.comp ((pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom := by
        have h := Scheme.Hom.germ_stalkMap (pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) U (e.hom.base (y.1.base (IsLocalRing.closedPoint k))) hzW
        have h' := congrArg CommRingCat.Hom.hom h
        simp only [CommRingCat.hom_comp] at h'
        exact h'
      have hcoreP : (IsLocalRing.maximalIdeal (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))))).map fsm = IsLocalRing.maximalIdeal ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.stalk (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))) := by
        rw [hmax0, Ideal.map_map]
        show Ideal.map (fsm.comp (M₀.C.presheaf.germ U (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))) hzU).hom) _ = _
        rw [hgsm, ← Ideal.map_map, ← h𝔭', hmaxP]
        rfl

      have hstc : (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).stalkMap (y.1.base (IsLocalRing.closedPoint k))).hom = ((e.hom.stalkMap (y.1.base (IsLocalRing.closedPoint k))).hom).comp fsm := by
        rw [Scheme.Hom.stalkMap_comp]
        rfl
      haveI : IsIso (e.hom.stalkMap (y.1.base (IsLocalRing.closedPoint k))) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
      have hcore : (IsLocalRing.maximalIdeal (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k))))).map (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).stalkMap (y.1.base (IsLocalRing.closedPoint k))).hom =
          IsLocalRing.maximalIdeal (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k))) := by
        rw [hstc, ← Ideal.map_map, hcoreP]

        let E := (asIso (e.hom.stalkMap (y.1.base (IsLocalRing.closedPoint k)))).commRingCatIsoToRingEquiv
        have hE : ∀ t, E t = (e.hom.stalkMap (y.1.base (IsLocalRing.closedPoint k))).hom t := fun t => rfl
        apply le_antisymm
        · rw [Ideal.map_le_iff_le_comap]
          intro t ht
          rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht
          intro hu
          exact ht ((isUnit_map_iff (e.hom.stalkMap (y.1.base (IsLocalRing.closedPoint k))).hom t).mp hu)
        · intro t ht
          have ht' : E.symm t ∈ IsLocalRing.maximalIdeal ((pullback M₀.toBase (Spec.map (CommRingCat.ofHom φ))).presheaf.stalk (e.hom.base (y.1.base (IsLocalRing.closedPoint k)))) := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
            intro hu
            apply ht
            have := hu.map E
            rwa [E.apply_symm_apply] at this
          have := Ideal.mem_map_of_mem ((e.hom.stalkMap (y.1.base (IsLocalRing.closedPoint k))).hom) ht'
          rwa [← hE, E.apply_symm_apply] at this

      have hR₀mem : ∀ t : (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))), (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t)) ∈ (M₀.pointEquivPlace y₀).toValuationSubring := fun t => by
        show _ ∈ (M₀.pointEquivPlace y₀).toValuationSubring.toSubring
        rw [← hQz₀]; exact ⟨t, rfl⟩
      have hRmem : ∀ u : (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k))), (M.ffEquiv.symm (algebraMap _ M.C.functionField u)) ∈ (M.pointEquivPlace y).toValuationSubring := fun u => by
        show _ ∈ (M.pointEquivPlace y).toValuationSubring.toSubring
        rw [← hQz]; exact ⟨u, rfl⟩
      have hR₀inj : Function.Injective (fun t : (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) => (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t))) := fun t t' h =>
        IsFractionRing.injective (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) M₀.C.functionField (M₀.ffEquiv.symm.injective h)
      have hR₀surj : ∀ x : F₀, x ∈ (M₀.pointEquivPlace y₀).toValuationSubring → ∃ t : (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))), (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t)) = x := by
        intro x hx
        have hx' : x ∈ (M₀.pointEquivPlace y₀).toValuationSubring.toSubring := hx
        rw [← hQz₀] at hx'
        obtain ⟨t, rfl⟩ := hx'
        exact ⟨t, rfl⟩
      have hRsurj : ∀ x : F, x ∈ (M.pointEquivPlace y).toValuationSubring → ∃ u : (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k))), (M.ffEquiv.symm (algebraMap _ M.C.functionField u)) = x := by
        intro x hx
        have hx' : x ∈ (M.pointEquivPlace y).toValuationSubring.toSubring := hx
        rw [← hQz] at hx'
        obtain ⟨u, rfl⟩ := hx'
        exact ⟨u, rfl⟩
      have hR₀nu : ∀ t : (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))), ¬ IsUnit t → (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t)) ∈ (M₀.pointEquivPlace y₀).toValuationSubring.nonunits := by
        intro t ht
        rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
        refine ⟨hR₀mem t, ?_⟩
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hunit
        apply ht
        obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hunit
        obtain ⟨t', ht'⟩ := hR₀surj (w : F₀) w.2
        refine isUnit_iff_exists_inv.mpr ⟨t', hR₀inj ?_⟩
        have h := congrArg Subtype.val hw
        show (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField (t * t'))) = (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField 1))
        rw [map_mul, map_mul, map_one, map_one, ht']
        exact h
      have hRunit : ∀ u : (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k))), IsUnit u → IsUnit (⟨(M.ffEquiv.symm (algebraMap _ M.C.functionField u)), hRmem u⟩ : (M.pointEquivPlace y).toValuationSubring) := by
        intro u hu
        obtain ⟨u', hu'⟩ := isUnit_iff_exists_inv.mp hu
        refine isUnit_iff_exists_inv.mpr ⟨⟨_, hRmem u'⟩, Subtype.ext ?_⟩
        show (M.ffEquiv.symm (algebraMap _ M.C.functionField u)) * (M.ffEquiv.symm (algebraMap _ M.C.functionField u')) = 1
        rw [← map_mul, ← map_mul, hu', map_one, map_one]

      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (M₀.pointEquivPlace y₀).toValuationSubring
      obtain ⟨t₀, ht₀⟩ := hR₀surj (ϖ : F₀) ϖ.2
      have hϖmax := hϖ.maximalIdeal_eq
      have ht₀max : IsLocalRing.maximalIdeal (M₀.C.presheaf.stalk (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)))) = Ideal.span {t₀} := by
        apply le_antisymm
        · intro s hs
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs
          obtain ⟨hsmem, hsmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp (hR₀nu s hs)
          rw [hϖmax, Ideal.mem_span_singleton'] at hsmax
          obtain ⟨c, hc⟩ := hsmax
          obtain ⟨t', ht'⟩ := hR₀surj (c : F₀) c.2
          rw [Ideal.mem_span_singleton']
          refine ⟨t', hR₀inj ?_⟩
          have h := congrArg Subtype.val hc
          show (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField (t' * t₀))) = (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField s))
          rw [map_mul, map_mul, ht', ht₀]
          exact h
        · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hu
          have hn : (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t₀)) ∈ (M₀.pointEquivPlace y₀).toValuationSubring.nonunits := by
            rw [ht₀]
            exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
              ⟨ϖ.2, by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hϖ.not_isUnit⟩
          obtain ⟨hmem', hmax'⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hn
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax'
          apply hmax'
          obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
          refine isUnit_iff_exists_inv.mpr ⟨⟨_, hR₀mem w⟩, Subtype.ext ?_⟩
          show (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField t₀)) * (M₀.ffEquiv.symm (algebraMap _ M₀.C.functionField w)) = 1
          rw [← map_mul, ← map_mul, hw, map_one, map_one]

      have hπmem : ψ (ϖ : F₀) ∈ (M.pointEquivPlace y).toValuationSubring := hsub _ ϖ.2
      have hπne : (⟨ψ (ϖ : F₀), hπmem⟩ : (M.pointEquivPlace y).toValuationSubring) ≠ 0 := by
        intro h
        have h' : ψ (ϖ : F₀) = 0 := congrArg Subtype.val h
        exact hϖ.ne_zero (Subtype.ext ((map_eq_zero ψ).mp h'))
      have hπmax : IsLocalRing.maximalIdeal (M.pointEquivPlace y).toValuationSubring = Ideal.span {⟨ψ (ϖ : F₀), hπmem⟩} := by
        apply le_antisymm
        · intro m hm
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
          obtain ⟨u, hu⟩ := hRsurj (m : F) m.2
          have hunu : ¬ IsUnit u := fun h => hm (by
            have := hRunit u h
            rwa [show (⟨(M.ffEquiv.symm (algebraMap _ M.C.functionField u)), hRmem u⟩ : (M.pointEquivPlace y).toValuationSubring) = m from Subtype.ext hu] at this)
          have humax : u ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k))) := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hunu
          rw [← hcore, ht₀max, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at humax
          obtain ⟨w, hw⟩ := humax
          rw [Ideal.mem_span_singleton']
          refine ⟨⟨_, hRmem w⟩, Subtype.ext ?_⟩
          show (M.ffEquiv.symm (algebraMap _ M.C.functionField w)) * ψ (ϖ : F₀) = (m : F)
          rw [← hu, ← hw, map_mul, map_mul, ← ht₀, hC t₀, mul_comm]
        · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
          obtain ⟨hmem', hmax'⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp
            (hnu _ (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
              ⟨ϖ.2, by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hϖ.not_isUnit⟩))
          exact hmax'
      have hπirr : Irreducible (⟨ψ (ϖ : F₀), hπmem⟩ : (M.pointEquivPlace y).toValuationSubring) :=
        IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hπne hπmax
      have hordπ : (M.pointEquivPlace y).ord (ψ (ϖ : F₀)) = 1 := (M.pointEquivPlace y).ord_coe_irreducible hπirr
      have hordϖ : (M₀.pointEquivPlace y₀).ord (ϖ : F₀) = 1 := (M₀.pointEquivPlace y₀).ord_coe_irreducible hϖ

      have hordu : ∀ u : ((M₀.pointEquivPlace y₀).toValuationSubring)ˣ, (M.pointEquivPlace y).ord (ψ ((u : (M₀.pointEquivPlace y₀).toValuationSubring) : F₀)) = 0 := by
        intro u
        have hmem1 : ψ ((u : (M₀.pointEquivPlace y₀).toValuationSubring) : F₀) ∈ (M.pointEquivPlace y).toValuationSubring := hsub _ (u : (M₀.pointEquivPlace y₀).toValuationSubring).2
        have hmem2 : ψ ((↑(u⁻¹) : (M₀.pointEquivPlace y₀).toValuationSubring) : F₀) ∈ (M.pointEquivPlace y).toValuationSubring := hsub _ (↑(u⁻¹) : (M₀.pointEquivPlace y₀).toValuationSubring).2
        have hU' : IsUnit (⟨_, hmem1⟩ : (M.pointEquivPlace y).toValuationSubring) := by
          refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem2⟩, Subtype.ext ?_⟩
          show ψ ((u : (M₀.pointEquivPlace y₀).toValuationSubring) : F₀) * ψ ((↑(u⁻¹) : (M₀.pointEquivPlace y₀).toValuationSubring) : F₀) = 1
          rw [← map_mul]
          have : ((u : (M₀.pointEquivPlace y₀).toValuationSubring) : F₀) * ((↑(u⁻¹) : (M₀.pointEquivPlace y₀).toValuationSubring) : F₀) = 1 := by
            rw [← MulMemClass.coe_mul, u.mul_inv]
            rfl
          rw [this, map_one]
        obtain ⟨w, hw⟩ := hU'
        have := (M.pointEquivPlace y).ord_coe_unit w
        rw [hw] at this
        exact this

      have hmain : ∀ g : F₀, g ∈ (M₀.pointEquivPlace y₀).toValuationSubring → (M.pointEquivPlace y).ord (ψ g) = (M₀.pointEquivPlace y₀).ord g := by
        intro g hg
        rcases eq_or_ne g 0 with rfl | hg0
        · rw [map_zero, (M.pointEquivPlace y).ord_zero, (M₀.pointEquivPlace y₀).ord_zero]
        have hg0' : (⟨g, hg⟩ : (M₀.pointEquivPlace y₀).toValuationSubring) ≠ 0 := fun h => hg0 (congrArg Subtype.val h)
        obtain ⟨n, u, hgu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0' hϖ
        have hgF : g = ((u : (M₀.pointEquivPlace y₀).toValuationSubring) : F₀) * (ϖ : F₀) ^ n := by
          have := congrArg Subtype.val hgu
          simpa using this
        have hψne : ∀ x : F₀, x ≠ 0 → ψ x ≠ 0 := fun x hx h => hx ((map_eq_zero ψ).mp h)
        have huF0 : ((u : (M₀.pointEquivPlace y₀).toValuationSubring) : F₀) ≠ 0 := fun h => (u.isUnit.ne_zero) (Subtype.ext h)
        have hϖF0 : (ϖ : F₀) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
        rw [hgF, map_mul, map_pow, (M.pointEquivPlace y).ord_mul (hψne _ huF0) (pow_ne_zero n (hψne _ hϖF0)),
          (M₀.pointEquivPlace y₀).ord_mul huF0 (pow_ne_zero n hϖF0), hordu u, (M₀.pointEquivPlace y₀).ord_coe_unit u,
          ← zpow_natCast, ← zpow_natCast, (M.pointEquivPlace y).ord_zpow, (M₀.pointEquivPlace y₀).ord_zpow, hordπ, hordϖ]
      intro f
      rcases ((M₀.pointEquivPlace y₀).toValuationSubring).mem_or_inv_mem f with hf | hf
      · exact hmain f hf
      · have h := hmain f⁻¹ hf
        rw [map_inv₀, (M.pointEquivPlace y).ord_inv, (M₀.pointEquivPlace y₀).ord_inv] at h
        exact neg_injective h
  ·
    intro Q hQ f hf

    obtain ⟨y, rfl⟩ := M.pointEquivPlace.surjective Q
    have hQz : ((M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
        (algebraMap (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k))) M.C.functionField)).range =
        (M.pointEquivPlace y).toValuationSubring.toSubring := by
      rw [CurveModel.pointEquivPlace_apply]
      exact M.range_stalk_eq (pointEquivClosedPoint M.toBase y)

    have hbase : (y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))) ≫ M₀.toBase = Spec.map (CommRingCat.ofHom φ) := by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, he, ← Category.assoc, y.2,
        Category.id_comp]
    by_cases hcl : IsClosed ({(y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (IsLocalRing.closedPoint k)} : Set M₀.C)
    ·
      exfalso
      let y₀' := pointOfClosedPoint M₀.toBase _ hcl
      have hover : y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) = Spec.map (CommRingCat.ofHom φ) ≫ y₀' := by

        have hL := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k M₀.C (y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))))

        set α := M₀.C.descResidueField (Scheme.stalkClosedPointTo (y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))))) with hαdef
        have hα : (residueFieldIsoBase M₀.toBase _ hcl).inv ≫ α = CommRingCat.ofHom φ := by
          apply Spec.map_injective
          rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv, ← Category.assoc, hL]
          exact hbase
        have hα' : α = (residueFieldIsoBase M₀.toBase _ hcl).hom ≫ CommRingCat.ofHom φ := by
          rw [← cancel_epi (residueFieldIsoBase M₀.toBase _ hcl).inv, Iso.inv_hom_id_assoc]
          exact hα
        rw [← hL, hα', Spec.map_comp, Category.assoc]
        rfl
      exact hQ ⟨y₀', pointOfClosedPoint_comp M₀.toBase _ hcl⟩ y hover rfl
    ·
      have hgen : (y.1 ≫ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (IsLocalRing.closedPoint k) = genericPoint M₀.C := by
        by_contra hne
        exact hcl (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M₀.toBase _ hne)

      have hmem : ∀ g : F₀, ψ g ∈ (M.pointEquivPlace y).toValuationSubring := by
        intro g

        obtain ⟨U, hηU, s, hs⟩ := TopCat.Presheaf.germ_exist M₀.C.presheaf (x := genericPoint M₀.C) (M₀.ffEquiv g)
        haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨genericPoint M₀.C, hηU⟩⟩
        have hzU : y.1.base (IsLocalRing.closedPoint k) ∈ (e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U := by
          show ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ)))).base (y.1.base (IsLocalRing.closedPoint k)) ∈ U
          rw [← Scheme.Hom.comp_apply, hgen]
          exact hηU
        haveI : Nonempty (Scheme.Opens.toScheme ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U)) := ⟨⟨_, hzU⟩⟩
        have hg : g = M₀.ffEquiv.symm (M₀.C.germToFunctionField U s) := by
          apply M₀.ffEquiv.injective
          rw [RingEquiv.apply_symm_apply]
          exact hs.symm
        have h1 : ψ g = M.ffEquiv.symm (M.C.germToFunctionField ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom s)) := by
          rw [hg, hsq]

        have h2 : M.ffEquiv.symm (M.C.germToFunctionField ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom s)) ∈
            ((M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
              (algebraMap (M.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k))) M.C.functionField)).range := by
          refine ⟨(M.C.presheaf.germ ((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ U) (y.1.base (IsLocalRing.closedPoint k)) hzU).hom
            (((e.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom φ))).app U).hom s), ?_⟩
          show M.ffEquiv.symm (algebraMap _ M.C.functionField _) = _
          congr 1
          show (M.C.presheaf.germ _ _ hzU ≫ M.C.presheaf.stalkSpecializes _).hom _ = _
          rw [TopCat.Presheaf.germ_stalkSpecializes]
        rw [h1]
        have h3 := hQz ▸ h2
        exact h3

      have hu : IsUnit (⟨ψ f, hmem f⟩ : (M.pointEquivPlace y).toValuationSubring) := by
        refine isUnit_iff_exists_inv.mpr ⟨⟨ψ f⁻¹, hmem f⁻¹⟩, ?_⟩
        apply Subtype.ext
        show ψ f * ψ f⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ hf, map_one]
      obtain ⟨u, hu'⟩ := hu
      have := (M.pointEquivPlace y).ord_coe_unit u
      rw [hu'] at this
      exact this

end
end S_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq (solution)
