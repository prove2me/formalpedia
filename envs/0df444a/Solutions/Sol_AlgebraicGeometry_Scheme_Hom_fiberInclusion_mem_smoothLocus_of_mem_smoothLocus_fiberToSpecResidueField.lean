-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5165a701-bb88-5b23-b69b-4363cb7df450

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_Algebra_isSmoothAt_of_isSmoothAt_fiber
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Hom.preimage_smoothLocus_eq Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd LocallyOfFinitePresentation.finitePresentation_appLE formallySmooth_stalkMap_iff Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top Scheme.Spec.residueFieldIso IsAffineOpen.SpecMap_appLE_fromSpec Spec isPullback_fiberToSpecResidueField_of_isPullback Scheme.Hom.stalkMap_comp Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion Scheme.Opens.topIso_hom Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus Scheme.Spec IsAffineOpen Smooth.smooth_appLE Flat.comp pullbackRestrictIsoRestrict FormallyUnramified Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE LocallyOfFinitePresentation Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField IsAffineHom Scheme.Opens.ι_appTop Scheme.Hom.comp_apply Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE fromSpecResidueField Hom.preimage_smoothLocus_eq Opens.topIso_inv Hom Γ topIso_hom Spec.residueFieldIso topIso Hom.stalkMap_comp ΓSpecIso_inv_naturality isoSpec_Spec_inv Opens.topIso_hom Hom.comp_base Hom.comp_appTop isoSpec residueField Hom.mem_smoothLocus isBasis_affineOpens Opens residue Hom.appLE_map Hom.app_eq_appLE Spec.map_residueFieldIso_inv_eq_fromSpecResidueField Opens.ι_appTop Hom.comp_apply Hom.appLE ΓSpecIso TwoAffineOpenCover"
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
end AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Hom.preimage_smoothLocus_eq Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd LocallyOfFinitePresentation.finitePresentation_appLE formallySmooth_stalkMap_iff Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top Scheme.Spec.residueFieldIso IsAffineOpen.SpecMap_appLE_fromSpec Spec isPullback_fiberToSpecResidueField_of_isPullback Scheme.Hom.stalkMap_comp Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion Scheme.Opens.topIso_hom Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus Scheme.Spec IsAffineOpen Smooth.smooth_appLE Flat.comp pullbackRestrictIsoRestrict FormallyUnramified Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE LocallyOfFinitePresentation Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField IsAffineHom Scheme.Opens.ι_appTop Scheme.Hom.comp_apply Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover"
namespace SmoothFibre
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
variable (k : Type u) [Field k] [Algebra R k]

scoped instance : IsAffineHom (specMap R k) := by unfold specMap; infer_instance

scoped instance : IsAffineHom (fst c k) := MorphismProperty.pullback_fst _ _ inferInstance

theorem isAffineOpen_preimage_fst (U : X.Opens) (hU : IsAffineOpen U) : IsAffineOpen ((fst c k) ⁻¹ᵁ U) :=
  hU.preimage (fst c k)

theorem smooth_tensor_of_smooth_snd (U : X.Opens) (hU : IsAffineOpen U) (hsm : Smooth (snd c k)) :
    letI := algebraOfHom c U
    Algebra.Smooth k (k ⊗[R] Γ(X, U)) := by
  letI := algebraOfHom c U
  letI := algebraOfHom (snd c k) ((fst c k) ⁻¹ᵁ U)

  have h1 : (Scheme.Hom.appLE (snd c k) ⊤ ((fst c k) ⁻¹ᵁ U) le_top).hom.Smooth :=
    Smooth.smooth_appLE (snd c k) (isAffineOpen_top _) (isAffineOpen_preimage_fst c k U hU) le_top
  have h2 : ((Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Hom.appLE (snd c k) ⊤ ((fst c k) ⁻¹ᵁ U) le_top).hom.Smooth := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.bijective) h1
  have h3 : Algebra.Smooth k Γ(XA c k, (fst c k) ⁻¹ᵁ U) := h2
  exact Algebra.Smooth.of_equiv (algEquiv c k U hU).symm

end AlgebraicGeometry.SmoothFibre
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry.SmoothFibre"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry"

namespace Algebra p2m_export "Algebra" "FormallySmooth ofId map_top FormallyUnramified.of_surjective FormallySmooth.of_equiv Smooth.of_equiv TensorProduct.includeRight algebraMap FormallyUnramified FormallySmooth.comp smoothLocus TensorProduct.comm TensorProduct.algebraMap_apply Smooth IsSmoothAt Smooth.comp id TensorProduct.comm_tmul Smooth.of_smooth_tensorProduct_of_faithfullyFlat TensorProduct.cancelBaseChange IsSmoothAt.of_formallySmooth_fiber FormallySmooth.of_restrictScalars TensorProduct.includeLeftRingHom FinitePresentation isSmoothAt_of_isSmoothAt_fiber IsSmoothAt.comap_algEquiv IsSmoothAt.of_algEquiv_of_comap_eq" end Algebra
p2m_open_scoped "Algebra" in

theorem Algebra.isSmoothAt_of_smooth_tensorProduct_field
    {R S k : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra.FinitePresentation R S]
    [Field k] [Algebra R k] [Algebra.Smooth k (k ⊗[R] S)]
    (q : Ideal S) [q.IsPrime] (hq : q.under R = RingHom.ker (algebraMap R k)) : Algebra.IsSmoothAt R q := by
  set p : Ideal R := RingHom.ker (algebraMap R k) with hp
  haveI : p.IsPrime := RingHom.ker_isPrime _
  haveI : q.LiesOver p := ⟨hq.symm⟩

  let ψ : p.ResidueField →+* k := Ideal.ResidueField.lift p (algebraMap R k) le_rfl (by
    intro r hr
    change IsUnit (algebraMap R k r)
    have : algebraMap R k r ≠ 0 := fun h => hr (show r ∈ RingHom.ker (algebraMap R k) from h)
    exact isUnit_iff_ne_zero.mpr this)
  letI : Algebra p.ResidueField k := ψ.toAlgebra
  haveI : IsScalarTower R p.ResidueField k := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R k r = ψ (algebraMap R p.ResidueField r)
    rw [Ideal.ResidueField.lift_algebraMap])
  haveI : Module.FaithfullyFlat p.ResidueField k := inferInstance

  let e : k ⊗[p.ResidueField] (p.ResidueField ⊗[R] S) ≃ₐ[k] k ⊗[R] S :=
    Algebra.TensorProduct.cancelBaseChange R p.ResidueField k k S
  haveI : Algebra.Smooth k (k ⊗[p.ResidueField] (p.Fiber S)) := Algebra.Smooth.of_equiv e.symm
  haveI : Algebra.Smooth p.ResidueField (p.Fiber S) := Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat k
  exact Algebra.IsSmoothAt.of_formallySmooth_fiber p q

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Hom.preimage_smoothLocus_eq Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd LocallyOfFinitePresentation.finitePresentation_appLE formallySmooth_stalkMap_iff Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top Scheme.Spec.residueFieldIso IsAffineOpen.SpecMap_appLE_fromSpec Spec isPullback_fiberToSpecResidueField_of_isPullback Scheme.Hom.stalkMap_comp Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion Scheme.Opens.topIso_hom Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus Scheme.Spec IsAffineOpen Smooth.smooth_appLE Flat.comp pullbackRestrictIsoRestrict FormallyUnramified Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE LocallyOfFinitePresentation Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField IsAffineHom Scheme.Opens.ι_appTop Scheme.Hom.comp_apply Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover"
namespace SmoothFibre
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
variable (k : Type u) [Field k] [Algebra R k]

theorem base_fst_asIdeal (z : ↥(XA c k)) :
    (c.base ((fst c k).base z)).asIdeal = RingHom.ker (algebraMap R k) := by
  have h : c.base ((fst c k).base z) = (specMap R k).base ((snd c k).base z) := by
    have := congrArg (fun f => f.base z) (pullback.condition (f := c) (g := specMap R k))
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using this
  rw [h]
  have hpt : (snd c k).base z = ⟨⊥, Ideal.isPrime_bot⟩ := Subsingleton.elim _ _
  rw [hpt]
  show (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap R k)).hom ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, ← RingHom.ker_eq_comap_bot]

theorem comap_ΓSpecIso_inv_primeIdealOf_top (p : ↥(Spec (CommRingCat.of R))) :
    Ideal.comap (Scheme.ΓSpecIso (.of R)).inv.hom ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨p, trivial⟩).asIdeal =
      p.asIdeal := by
  have h := (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec_primeIdealOf ⟨p, trivial⟩
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h

  have h' : PrimeSpectrum.comap (Scheme.ΓSpecIso (.of R)).inv.hom
      ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨p, trivial⟩) = p := h
  rw [← PrimeSpectrum.comap_asIdeal, h']

variable [Flat c] [LocallyOfFinitePresentation c]

private theorem _root_.Algebra.IsSmoothAt.comap_algEquiv {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) (Q : Ideal B) [Q.IsPrime] [Algebra.IsSmoothAt K Q] :
    Algebra.IsSmoothAt K (Q.comap e.toRingHom) := by
  set P := Q.comap e.toRingHom with hP
  have hQP : Q = P.comap e.symm.toRingHom := by
    ext b
    show b ∈ Q ↔ e (e.symm b) ∈ Q
    rw [e.apply_symm_apply]
  let φ : Localization.AtPrime P →+* Localization.AtPrime Q := Localization.localRingHom P Q e.toRingHom hP
  let ψ : Localization.AtPrime Q →+* Localization.AtPrime P := Localization.localRingHom Q P e.symm.toRingHom hQP
  have h1 : ψ.comp φ = RingHom.id _ := by
    refine IsLocalization.ringHom_ext P.primeCompl ?_
    ext a
    simp [φ, ψ, Localization.localRingHom_to_map]
  have h2 : φ.comp ψ = RingHom.id _ := by
    refine IsLocalization.ringHom_ext Q.primeCompl ?_
    ext b
    simp [φ, ψ, Localization.localRingHom_to_map]
  let E₀ : Localization.AtPrime P ≃+* Localization.AtPrime Q := RingEquiv.ofRingHom φ ψ h2 h1
  let E : Localization.AtPrime P ≃ₐ[K] Localization.AtPrime Q :=
    AlgEquiv.ofRingEquiv (f := E₀) (fun x => by
      show φ (algebraMap K _ x) = algebraMap K _ x
      rw [IsScalarTower.algebraMap_apply K A (Localization.AtPrime P), Localization.localRingHom_to_map,
        IsScalarTower.algebraMap_apply K B (Localization.AtPrime Q)]
      simp)
  exact Algebra.FormallySmooth.of_equiv E.symm

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.Algebra.IsSmoothAt.comap_algEquiv" "Algebra.IsSmoothAt.comap_algEquiv"

private theorem _root_.Algebra.IsSmoothAt.of_algEquiv_of_comap_eq {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : Q.comap e.toRingHom = P) [Algebra.IsSmoothAt K Q] : Algebra.IsSmoothAt K P := by
  subst h
  exact Algebra.IsSmoothAt.comap_algEquiv e Q

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.Algebra.IsSmoothAt.of_algEquiv_of_comap_eq" "Algebra.IsSmoothAt.of_algEquiv_of_comap_eq"

theorem mem_smoothLocus_of_mem_smoothLocus_snd_residueField (p : Ideal R) [p.IsPrime]
    (z : ↥(XA c p.ResidueField)) (hz : z ∈ (snd c p.ResidueField).smoothLocus) :
    (fst c p.ResidueField).base z ∈ c.smoothLocus := by
  classical
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show (fst c p.ResidueField).base z ∈ (⊤ : X.Opens) from trivial)
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) V hV le_top hxV]
  letI instR' : Algebra Γ(Spec (.of R), ⊤) Γ(X, V) := (c.appLE ⊤ V le_top).hom.toAlgebra
  change Algebra.IsSmoothAt Γ(Spec (.of R), ⊤) (hV.primeIdealOf ⟨_, hxV⟩).asIdeal

  letI := algebraOfHom c V
  have hbij : Function.Bijective (Scheme.ΓSpecIso (.of R)).inv.hom :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.bijective
  haveI : Module.Flat R Γ(X, V) := by
    have h : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.Flat := by
      rw [CommRingCat.hom_comp]
      exact RingHom.Flat.comp (RingHom.Flat.of_bijective hbij) (Flat.flat_appLE c (isAffineOpen_top _) hV le_top)
    exact h
  haveI : Algebra.FinitePresentation R Γ(X, V) := by
    have h : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.FinitePresentation := by
      rw [CommRingCat.hom_comp]
      exact RingHom.FinitePresentation.comp
        (LocallyOfFinitePresentation.finitePresentation_appLE c (isAffineOpen_top _) hV le_top)
        (RingHom.FinitePresentation.of_bijective hbij)
    exact h

  have hq : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.under R = p := by
    rw [Ideal.under_def, show algebraMap R Γ(X, V) = (c.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
      from by rw [← CommRingCat.hom_comp]; rfl, ← Ideal.comap_comap, ← PrimeSpectrum.comap_asIdeal,
      IsAffineOpen.comap_primeIdealOf_appLE ⊤ (isAffineOpen_top _) V hV le_top hxV,
      comap_ΓSpecIso_inv_primeIdealOf_top, base_fst_asIdeal, Ideal.ker_algebraMap_residueField]
  haveI : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.LiesOver p := ⟨hq.symm⟩

  have hV' : IsAffineOpen ((fst c p.ResidueField) ⁻¹ᵁ V) := isAffineOpen_preimage_fst c p.ResidueField V hV
  have hzV' : z ∈ (fst c p.ResidueField) ⁻¹ᵁ V := hxV
  letI := algebraOfHom (snd c p.ResidueField) ((fst c p.ResidueField) ⁻¹ᵁ V)

  have hQ₀ : Algebra.IsSmoothAt p.ResidueField (hV'.primeIdealOf ⟨z, hzV'⟩).asIdeal := by
    have h := hz
    rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) _ hV' le_top hzV'] at h
    letI instk' : Algebra Γ(Spec (.of p.ResidueField), ⊤) Γ(XA c p.ResidueField, (fst c p.ResidueField) ⁻¹ᵁ V) :=
      ((snd c p.ResidueField).appLE ⊤ _ le_top).hom.toAlgebra
    change Algebra.IsSmoothAt Γ(Spec (.of p.ResidueField), ⊤) (hV'.primeIdealOf ⟨z, hzV'⟩).asIdeal at h
    letI : Algebra p.ResidueField Γ(Spec (.of p.ResidueField), ⊤) :=
      (Scheme.ΓSpecIso (.of p.ResidueField)).inv.hom.toAlgebra
    haveI : IsScalarTower p.ResidueField Γ(Spec (.of p.ResidueField), ⊤)
        Γ(XA c p.ResidueField, (fst c p.ResidueField) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq (fun r => rfl)
    have hbijk : Function.Bijective (Scheme.ΓSpecIso (.of p.ResidueField)).inv.hom :=
      (Scheme.ΓSpecIso (.of p.ResidueField)).commRingCatIsoToRingEquiv.symm.bijective
    haveI : Algebra.FormallySmooth p.ResidueField Γ(Spec (.of p.ResidueField), ⊤) :=
      Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId p.ResidueField _) hbijk)
    haveI := h
    exact Algebra.FormallySmooth.comp p.ResidueField Γ(Spec (.of p.ResidueField), ⊤)
      (Localization.AtPrime (hV'.primeIdealOf ⟨z, hzV'⟩).asIdeal)

  let e := algEquiv c p.ResidueField V hV
  let Q : Ideal (p.Fiber Γ(X, V)) := (hV'.primeIdealOf ⟨z, hzV'⟩).asIdeal.comap e.toRingHom
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  haveI hQsm : Algebra.IsSmoothAt p.ResidueField Q := Algebra.IsSmoothAt.comap_algEquiv e _
  have hQ : Q.comap (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[R] p.Fiber Γ(X, V)).toRingHom
      = (hV.primeIdealOf ⟨_, hxV⟩).asIdeal := by
    have hcomp : e.toRingHom.comp (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[R] p.Fiber Γ(X, V)).toRingHom
        = ((fst c p.ResidueField).app V).hom := by
      ext s
      exact algEquiv_one_tmul c p.ResidueField V hV s
    show Ideal.comap _ (Ideal.comap _ _) = _
    rw [Ideal.comap_comap, hcomp, Scheme.Hom.app_eq_appLE]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (f := fst c p.ResidueField) V hV _ hV' le_rfl hzV')

  have hR : Algebra.IsSmoothAt R (hV.primeIdealOf ⟨_, hxV⟩).asIdeal :=
    Algebra.isSmoothAt_of_isSmoothAt_fiber p _ Q hQ

  letI : Algebra R Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv.hom.toAlgebra
  haveI : IsScalarTower R Γ(Spec (.of R), ⊤) Γ(X, V) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Algebra.FormallyUnramified R Γ(Spec (.of R), ⊤) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId R Γ(Spec (.of R), ⊤)) hbij.2
  exact Algebra.FormallySmooth.of_restrictScalars R Γ(Spec (.of R), ⊤)
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal)

private theorem _root_.AlgebraicGeometry.SmoothFibre.smoothLocus_comp_of_isOpenImmersion {X' Y Z : Scheme.{u}} (f : X' ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (f ≫ g)] [IsOpenImmersion g] :
    (f ≫ g).smoothLocus = f.smoothLocus := by
  ext x
  show ((f ≫ g).stalkMap x).hom.FormallySmooth ↔ (f.stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _

p2m_export "AlgebraicGeometry.SmoothFibre" "smoothLocus_comp_of_isOpenImmersion"

private theorem _root_.AlgebraicGeometry.SmoothFibre.smoothLocus_congr {X' Y : Scheme.{u}} {f g : X' ⟶ Y}
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) :
    f.smoothLocus = g.smoothLocus := by
  subst h
  rfl

p2m_export "AlgebraicGeometry.SmoothFibre" "smoothLocus_congr"

theorem H1_affine {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation c] [Flat c] (y : ↥(Spec (CommRingCat.of R)))
    [LocallyOfFinitePresentation (c.fiberToSpecResidueField y)]
    (z : ↥(c.fiber y)) (hz : z ∈ (c.fiberToSpecResidueField y).smoothLocus) :
    (c.fiberι y).base z ∈ c.smoothLocus := by
  let ι : Spec ((Spec (CommRingCat.of R)).residueField y) ⟶ Spec (CommRingCat.of y.asIdeal.ResidueField) :=
    Spec.map (Scheme.Spec.residueFieldIso (.of R) y).inv
  have hι : ι ≫ specMap R y.asIdeal.ResidueField = (Spec (CommRingCat.of R)).fromSpecResidueField y :=
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) y
  let m : c.fiber y ⟶ XA c y.asIdeal.ResidueField :=
    pullback.map c ((Spec (CommRingCat.of R)).fromSpecResidueField y) c (specMap R y.asIdeal.ResidueField) (𝟙 X) ι (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι])
  haveI : IsIso ι := by simp only [ι]; infer_instance
  haveI : IsIso m := pullback.map_isIso c ((Spec (CommRingCat.of R)).fromSpecResidueField y) c
    (specMap R y.asIdeal.ResidueField) (𝟙 X) ι (𝟙 _) _ _
  have hm_fst : m ≫ fst c y.asIdeal.ResidueField = c.fiberι y := by
    simp only [m, pullback.map, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hm_snd : m ≫ snd c y.asIdeal.ResidueField = c.fiberToSpecResidueField y ≫ ι := by
    simp only [m, pullback.map, Category.comp_id]
    exact pullback.lift_snd _ _ _

  have hz' : m.base z ∈ (snd c y.asIdeal.ResidueField).smoothLocus := by
    have h1 : z ∈ (c.fiberToSpecResidueField y ≫ ι).smoothLocus := by
      rw [smoothLocus_comp_of_isOpenImmersion]
      exact hz
    rw [smoothLocus_congr hm_snd.symm, ← Scheme.Hom.preimage_smoothLocus_eq] at h1
    exact h1
  have h := mem_smoothLocus_of_mem_smoothLocus_snd_residueField c y.asIdeal (m.base z) hz'
  have hmz : (fst c y.asIdeal.ResidueField).base (m.base z) = (c.fiberι y).base z := by
    rw [← Scheme.Hom.comp_apply, hm_fst]
  rwa [hmz] at h

end AlgebraicGeometry.SmoothFibre
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry.SmoothFibre"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry.SmoothFibre"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry.SmoothFibre"

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Hom.preimage_smoothLocus_eq Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd LocallyOfFinitePresentation.finitePresentation_appLE formallySmooth_stalkMap_iff Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top Scheme.Spec.residueFieldIso IsAffineOpen.SpecMap_appLE_fromSpec Spec isPullback_fiberToSpecResidueField_of_isPullback Scheme.Hom.stalkMap_comp Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc IsOpenImmersion Scheme.Opens.topIso_hom Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus Scheme.Spec IsAffineOpen Smooth.smooth_appLE Flat.comp pullbackRestrictIsoRestrict FormallyUnramified Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE LocallyOfFinitePresentation Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField IsAffineHom Scheme.Opens.ι_appTop Scheme.Hom.comp_apply Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover"
p2m_open "AlgebraicGeometry"

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE fromSpecResidueField Hom.preimage_smoothLocus_eq Opens.topIso_inv Hom Γ topIso_hom Spec.residueFieldIso topIso Hom.stalkMap_comp ΓSpecIso_inv_naturality isoSpec_Spec_inv Opens.topIso_hom Hom.comp_base Hom.comp_appTop isoSpec residueField Hom.mem_smoothLocus isBasis_affineOpens Opens residue Hom.appLE_map Hom.app_eq_appLE Spec.map_residueFieldIso_inv_eq_fromSpecResidueField Opens.ι_appTop Hom.comp_apply Hom.appLE ΓSpecIso TwoAffineOpenCover" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "map_appLE preimage_smoothLocus_eq app smoothLocus fiber stalkMap_comp smooth_appLE stalkMap appTop comp_base comp_appTop comp_app fiberι residueFieldMap mem_smoothLocus flat_appLE ker finitePresentation_appLE appLE_map app_eq_appLE fiberToSpecResidueField comp_apply appLE" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.smoothLocus_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] : f.smoothLocus = g.smoothLocus := by
  subst h; rfl

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.smoothLocus_comp_of_isOpenImmersion {X Y Z : Scheme.{u}} (φ : X ⟶ Y) (e : Y ⟶ Z)
    [LocallyOfFinitePresentation φ] [IsOpenImmersion e] :
    (φ ≫ e).smoothLocus = φ.smoothLocus := by
  ext x
  change ((φ ≫ e).stalkMap x).hom.FormallySmooth ↔ (φ.stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _

private theorem _root_.H1GenY.fiberInclusion_mem_smoothLocus_general
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [Flat f] (y : ↥Y)
    [LocallyOfFinitePresentation (f.fiberToSpecResidueField y)] (z : ↥(f.fiber y))
    (hz : z ∈ (f.fiberToSpecResidueField y).smoothLocus) :
    (f.fiberι y).base z ∈ f.smoothLocus := by

  obtain ⟨U, hU, hyU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  haveI : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hyr : y ∈ Set.range ⇑hU.fromSpec := by rw [hU.range_fromSpec]; exact hyU
  obtain ⟨y', rfl⟩ := hyr

  set f' := pullback.snd f hU.fromSpec with hf'
  haveI : LocallyOfFinitePresentation f' := MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  haveI : LocallyOfFinitePresentation (f'.fiberToSpecResidueField y') :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance

  have hsq := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f hU.fromSpec) y'
  set m := pullback.map f' ((Spec Γ(Y, U)).fromSpecResidueField y') f (Y.fromSpecResidueField (hU.fromSpec y'))
    (pullback.fst f hU.fromSpec) (Spec.map (hU.fromSpec.residueFieldMap y')) hU.fromSpec (IsPullback.of_hasPullback f hU.fromSpec).w.symm (by simp) with hm
  haveI : IsIso m := hsq.isIso_fst_of_isIso

  set z' : ↥(f'.fiber y') := (inv m).base z with hz'
  have hmz' : m.base z' = z := by
    change (inv m ≫ m).base z = z
    rw [IsIso.inv_hom_id]; rfl

  have hz'sm : z' ∈ (f'.fiberToSpecResidueField y').smoothLocus := by
    rw [Scheme.Hom.mem_smoothLocus]

    have h1 : ((m ≫ f.fiberToSpecResidueField (hU.fromSpec y')).stalkMap z').hom.FormallySmooth := by
      rw [Scheme.Hom.stalkMap_comp]
      refine (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).mpr ?_
      have hz0 := hz
      rw [Scheme.Hom.mem_smoothLocus, ← hmz'] at hz0
      exact hz0
    rw [hsq.w, Scheme.Hom.stalkMap_comp] at h1
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mp h1

  have haff := SmoothFibre.H1_affine f' y' z' hz'sm

  have hfst : (pullback.fst f hU.fromSpec) ⁻¹ᵁ f.smoothLocus = f'.smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_congr pullback.condition,
      Scheme.Hom.smoothLocus_comp_of_isOpenImmersion]
  have hmfst : m ≫ f.fiberι (hU.fromSpec y') = f'.fiberι y' ≫ pullback.fst f hU.fromSpec := pullback.lift_fst _ _ _
  have : (f.fiberι (hU.fromSpec y')).base z = (pullback.fst f hU.fromSpec).base ((f'.fiberι y').base z') := by
    rw [← hmz']
    exact congrArg (fun φ => φ.base z') hmfst
  rw [this]
  change (f'.fiberι y').base z' ∈ (pullback.fst f hU.fromSpec) ⁻¹ᵁ f.smoothLocus
  rw [hfst]
  exact haff

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.H1GenY.fiberInclusion_mem_smoothLocus_general" "H1GenY.fiberInclusion_mem_smoothLocus_general"
end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry.SmoothFibre"

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField.AlgebraicGeometry in
theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [Flat f] (y : ↥Y)
    [LocallyOfFinitePresentation (f.fiberToSpecResidueField y)] (z : ↥(f.fiber y))
    (hz : z ∈ (f.fiberToSpecResidueField y).smoothLocus) :
    (f.fiberι y).base z ∈ f.smoothLocus := by
  exact H1GenY.fiberInclusion_mem_smoothLocus_general f y z hz

end S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField (solution)
