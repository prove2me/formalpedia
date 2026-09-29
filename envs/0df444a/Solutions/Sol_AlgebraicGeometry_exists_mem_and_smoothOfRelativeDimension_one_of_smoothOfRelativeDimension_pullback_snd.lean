-- Prove2me | solution 1 for AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0208c349-9eee-5ebc-ad5a-10109d1e66b0

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp HasRingHomProperty.iff_of_isAffine Scheme.Hom.map_appLE SmoothOfRelativeDimension.smooth Scheme.Hom.preimage_smoothLocus_eq Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd LocallyOfFinitePresentation.finitePresentation_appLE formallySmooth_stalkMap_iff SmoothOfRelativeDimension Scheme.Hom Scheme.Hom.smoothLocus_eq_top_iff Scheme.Γ IsAffineOpen.fromSpec_top IsAffine IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Spec.map_surjective Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst HasRingHomProperty.appLE exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus IsAffineOpen Smooth.smooth_appLE Flat.comp pullbackRestrictIsoRestrict FormallyUnramified Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE LocallyOfFinitePresentation IsAffineHom Scheme.Opens.ι_appTop HasRingHomProperty Scheme.Opens.ι_preimage_self Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Hom.preimage_smoothLocus_eq Opens.topIso_inv Hom Hom.smoothLocus_eq_top_iff Γ topIso_hom topIso ΓSpecIso_inv_naturality isoSpec_Spec_inv Opens.topIso_hom Hom.comp_base Hom.comp_appTop isoSpec basicOpen Hom.mem_smoothLocus Opens residue Hom.appLE_map Hom.app_eq_appLE Opens.ι_appTop Opens.ι_preimage_self basicOpen_le Hom.appLE ΓSpecIso TwoAffineOpenCover"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom algebraMap_algebraOfHom restrictAlgHom pullback"
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

private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    (A ⊗[R] Γ(X, U)) ≃ₐ[A] Γ(XA c A, (fst c A) ⁻¹ᵁ U) :=
  letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R A Γ(X, U)).toRingEquiv.trans (sigma c A U hU))
    (fun a => by
      show sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) (algebraMap A (A ⊗[R] Γ(X, U)) a)) = _
      rw [Algebra.TensorProduct.algebraMap_apply, show algebraMap A A a = a from rfl,
        Algebra.TensorProduct.comm_tmul, sigma_one_tmul, algebraMap_sndAlgebra])

p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange" "algEquiv"
theorem algEquiv_one_tmul (s : Γ(X, U)) :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    algEquiv c A U hU ((1 : A) ⊗ₜ[R] s) = ((fst c A).app U).hom s := by
  letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  show sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) ((1 : A) ⊗ₜ[R] s)) = _
  rw [Algebra.TensorProduct.comm_tmul, sigma_tmul_one]

end AffineBaseChange
end AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp HasRingHomProperty.iff_of_isAffine Scheme.Hom.map_appLE SmoothOfRelativeDimension.smooth Scheme.Hom.preimage_smoothLocus_eq Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd LocallyOfFinitePresentation.finitePresentation_appLE formallySmooth_stalkMap_iff SmoothOfRelativeDimension Scheme.Hom Scheme.Hom.smoothLocus_eq_top_iff Scheme.Γ IsAffineOpen.fromSpec_top IsAffine IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Spec.map_surjective Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst HasRingHomProperty.appLE exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus IsAffineOpen Smooth.smooth_appLE Flat.comp pullbackRestrictIsoRestrict FormallyUnramified Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE LocallyOfFinitePresentation IsAffineHom Scheme.Opens.ι_appTop HasRingHomProperty Scheme.Opens.ι_preimage_self Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover"
namespace SmoothFibre
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.SmoothFibre"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry"

namespace Algebra p2m_export "Algebra" "FormallySmooth ofId map_top FormallyUnramified.of_surjective commutes Smooth.of_equiv TensorProduct.includeRight algebraMap FormallyUnramified IsStandardSmoothOfRelativeDimension.baseChange smoothLocus TensorProduct.comm TensorProduct.algebraMap_apply IsSmoothAt.exists_notMem_isStandardSmooth Smooth IsSmoothAt IsStandardSmooth.out IsStandardSmoothOfRelativeDimension.of_algEquiv IsStandardSmoothOfRelativeDimension Smooth.comp IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential IsStandardSmooth.of_algEquiv restrictScalars TensorProduct.comm_tmul IsStandardSmoothOfRelativeDimension.localization_away Smooth.of_smooth_tensorProduct_of_faithfullyFlat TensorProduct.cancelBaseChange IsStandardSmooth IsSmoothAt.of_formallySmooth_fiber FormallySmooth.of_restrictScalars IsStandardSmoothOfRelativeDimension.trans TensorProduct.includeLeftRingHom FinitePresentation" end Algebra
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
p2m_export "AlgebraicGeometry" "Spec.map_comp HasRingHomProperty.iff_of_isAffine Scheme.Hom.map_appLE SmoothOfRelativeDimension.smooth Scheme.Hom.preimage_smoothLocus_eq Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd LocallyOfFinitePresentation.finitePresentation_appLE formallySmooth_stalkMap_iff SmoothOfRelativeDimension Scheme.Hom Scheme.Hom.smoothLocus_eq_top_iff Scheme.Γ IsAffineOpen.fromSpec_top IsAffine IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Spec.map_surjective Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst HasRingHomProperty.appLE exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus IsAffineOpen Smooth.smooth_appLE Flat.comp pullbackRestrictIsoRestrict FormallyUnramified Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE LocallyOfFinitePresentation IsAffineHom Scheme.Opens.ι_appTop HasRingHomProperty Scheme.Opens.ι_preimage_self Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover"
namespace SmoothFibre
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange"

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

theorem mem_smoothLocus_of_smooth_snd (hsm : Smooth (snd c k)) (z : ↥(XA c k)) :
    (fst c k).base z ∈ c.smoothLocus := by
  classical
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (show (fst c k).base z ∈ (⊤ : X.Opens) from trivial)
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) V hV le_top hyV]
  letI instR' : Algebra Γ(Spec (.of R), ⊤) Γ(X, V) := (c.appLE ⊤ V le_top).hom.toAlgebra
  change Algebra.IsSmoothAt Γ(Spec (.of R), ⊤) (hV.primeIdealOf ⟨_, hyV⟩).asIdeal

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
  haveI : Algebra.Smooth k (k ⊗[R] Γ(X, V)) := smooth_tensor_of_smooth_snd c k V hV hsm

  have hq : (hV.primeIdealOf ⟨_, hyV⟩).asIdeal.under R = RingHom.ker (algebraMap R k) := by
    rw [Ideal.under_def, show algebraMap R Γ(X, V) = (c.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
      from by rw [← CommRingCat.hom_comp]; rfl, ← Ideal.comap_comap, ← PrimeSpectrum.comap_asIdeal,
      IsAffineOpen.comap_primeIdealOf_appLE ⊤ (isAffineOpen_top _) V hV le_top hyV,
      comap_ΓSpecIso_inv_primeIdealOf_top, base_fst_asIdeal]
  have hR : Algebra.IsSmoothAt R (hV.primeIdealOf ⟨_, hyV⟩).asIdeal :=
    Algebra.isSmoothAt_of_smooth_tensorProduct_field _ hq

  letI : Algebra R Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv.hom.toAlgebra
  haveI : IsScalarTower R Γ(Spec (.of R), ⊤) Γ(X, V) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Algebra.FormallyUnramified R Γ(Spec (.of R), ⊤) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId R Γ(Spec (.of R), ⊤)) hbij.2
  exact Algebra.FormallySmooth.of_restrictScalars R Γ(Spec (.of R), ⊤)
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hyV⟩).asIdeal)

end AlgebraicGeometry.SmoothFibre
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.SmoothFibre"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.SmoothFibre"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp HasRingHomProperty.iff_of_isAffine Scheme.Hom.map_appLE SmoothOfRelativeDimension.smooth Scheme.Hom.preimage_smoothLocus_eq Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd LocallyOfFinitePresentation.finitePresentation_appLE formallySmooth_stalkMap_iff SmoothOfRelativeDimension Scheme.Hom Scheme.Hom.smoothLocus_eq_top_iff Scheme.Γ IsAffineOpen.fromSpec_top IsAffine IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Spec.map_surjective Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst HasRingHomProperty.appLE exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus IsAffineOpen Smooth.smooth_appLE Flat.comp pullbackRestrictIsoRestrict FormallyUnramified Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE LocallyOfFinitePresentation IsAffineHom Scheme.Opens.ι_appTop HasRingHomProperty Scheme.Opens.ι_preimage_self Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover"
namespace SmoothFibre
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange"

theorem exists_mem_and_smooth_of_smooth_pullback_snd
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [Flat c] [LocallyOfFinitePresentation c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hsm : Smooth (pullback.snd c x)) :
    ∀ y ∈ Set.range (pullback.fst c x).base, ∃ W : C.Opens, y ∈ W ∧ Smooth (W.ι ≫ c) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  letI : Algebra R k := φ.hom.toAlgebra
  rintro y ⟨z, rfl⟩
  refine ⟨c.smoothLocus, mem_smoothLocus_of_smooth_snd c k hsm z, ?_⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, Scheme.Opens.ι_preimage_self]

theorem mem_smoothLocus_of_smooth_pullback_snd
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [Flat c] [LocallyOfFinitePresentation c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hsm : Smooth (pullback.snd c x)) :
    ∀ y ∈ Set.range (pullback.fst c x).base, y ∈ c.smoothLocus := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  letI : Algebra R k := φ.hom.toAlgebra
  rintro y ⟨z, rfl⟩
  exact mem_smoothLocus_of_smooth_snd c k hsm z

end AlgebraicGeometry.SmoothFibre
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.SmoothFibre"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.SmoothFibre"

namespace Algebra p2m_export "Algebra" "FormallySmooth ofId map_top FormallyUnramified.of_surjective commutes Smooth.of_equiv TensorProduct.includeRight algebraMap FormallyUnramified IsStandardSmoothOfRelativeDimension.baseChange smoothLocus TensorProduct.comm TensorProduct.algebraMap_apply IsSmoothAt.exists_notMem_isStandardSmooth Smooth IsSmoothAt IsStandardSmooth.out IsStandardSmoothOfRelativeDimension.of_algEquiv IsStandardSmoothOfRelativeDimension Smooth.comp IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential IsStandardSmooth.of_algEquiv restrictScalars TensorProduct.comm_tmul IsStandardSmoothOfRelativeDimension.localization_away Smooth.of_smooth_tensorProduct_of_faithfullyFlat TensorProduct.cancelBaseChange IsStandardSmooth IsSmoothAt.of_formallySmooth_fiber FormallySmooth.of_restrictScalars IsStandardSmoothOfRelativeDimension.trans TensorProduct.includeLeftRingHom FinitePresentation" namespace IsStandardSmooth p2m_export "Algebra.IsStandardSmooth" "baseChange out trans localization_away of_algEquiv" end Algebra.IsStandardSmooth
p2m_open_scoped "Algebra Algebra.IsStandardSmooth" in

theorem Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsStandardSmooth R A] :
    ∃ d : ℕ, Algebra.IsStandardSmoothOfRelativeDimension d R A := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := A)
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

p2m_open_scoped "Algebra" in

theorem Algebra.isStandardSmoothOfRelativeDimension_of_baseChange_localization
    {R A k : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsStandardSmooth R A]
    [Field k] [Algebra R k] (h : k ⊗[R] A) [Nontrivial (Localization.Away h)] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away h)] :
    Algebra.IsStandardSmoothOfRelativeDimension n R A := by
  obtain ⟨d, hd⟩ := Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension R A

  haveI : Algebra.IsStandardSmoothOfRelativeDimension d k (k ⊗[R] A) :=
    Algebra.IsStandardSmoothOfRelativeDimension.baseChange d k
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (k ⊗[R] A) (Localization.Away h) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away h
  haveI hd' : Algebra.IsStandardSmoothOfRelativeDimension (0 + d) k (Localization.Away h) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans d 0 k (k ⊗[R] A) (Localization.Away h)
  rw [zero_add] at hd'

  have h1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := Localization.Away h) n
  have h2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := Localization.Away h) d
  rw [h1] at h2
  have : n = d := by exact_mod_cast h2
  subst this
  exact hd

p2m_open_scoped "Algebra" in

theorem Algebra.isStandardSmoothOfRelativeDimension_of_baseChange_localization'
    {R A k B : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsStandardSmooth R A]
    [Field k] [Algebra R k] [CommRing B] [Algebra k B] (e : k ⊗[R] A ≃ₐ[k] B) (h : B) [Nontrivial (Localization.Away h)]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away h)] :
    Algebra.IsStandardSmoothOfRelativeDimension n R A := by
  obtain ⟨d, hd⟩ := Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension R A
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d k (k ⊗[R] A) :=
    Algebra.IsStandardSmoothOfRelativeDimension.baseChange d k
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d k B := Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv d e
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 B (Localization.Away h) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away h
  haveI hd' : Algebra.IsStandardSmoothOfRelativeDimension (0 + d) k (Localization.Away h) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans d 0 k B (Localization.Away h)
  rw [zero_add] at hd'
  have h1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := Localization.Away h) n
  have h2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := Localization.Away h) d
  rw [h1] at h2
  have : n = d := by exact_mod_cast h2
  subst this
  exact hd

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp HasRingHomProperty.iff_of_isAffine Scheme.Hom.map_appLE SmoothOfRelativeDimension.smooth Scheme.Hom.preimage_smoothLocus_eq Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd LocallyOfFinitePresentation.finitePresentation_appLE formallySmooth_stalkMap_iff SmoothOfRelativeDimension Scheme.Hom Scheme.Hom.smoothLocus_eq_top_iff Scheme.Γ IsAffineOpen.fromSpec_top IsAffine IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Smooth pullbackSpecIso Spec.map_surjective Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_base Scheme.Hom.comp_appTop Flat pullbackSpecIso_inv_fst HasRingHomProperty.appLE exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE Scheme.Hom.mem_smoothLocus IsAffineOpen Smooth.smooth_appLE Flat.comp pullbackRestrictIsoRestrict FormallyUnramified Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Flat.flat_appLE LocallyOfFinitePresentation IsAffineHom Scheme.Opens.ι_appTop HasRingHomProperty Scheme.Opens.ι_preimage_self Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover"
namespace SmoothFibre
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
variable (k : Type u) [Field k] [Algebra R k]

set_option maxHeartbeats 6400000 in

theorem exists_mem_and_smoothOfRelativeDimension_one_of_snd [Flat c] [LocallyOfFinitePresentation c]
    (hsm : SmoothOfRelativeDimension 1 (snd c k)) (z : ↥(XA c k)) :
    ∃ W : X.Opens, (fst c k).base z ∈ W ∧ SmoothOfRelativeDimension 1 (W.ι ≫ c) := by
  classical
  haveI : Smooth (snd c k) := SmoothOfRelativeDimension.smooth 1 _
  set y := (fst c k).base z with hy
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : X.Opens) from trivial)

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
  haveI : Algebra.Smooth k (k ⊗[R] Γ(X, V)) := smooth_tensor_of_smooth_snd c k V hV inferInstance
  set q := hV.primeIdealOf ⟨y, hyV⟩ with hqdef
  have hq : q.asIdeal.under R = RingHom.ker (algebraMap R k) := by
    rw [Ideal.under_def, show algebraMap R Γ(X, V) = (c.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
      from by rw [← CommRingCat.hom_comp]; rfl, ← Ideal.comap_comap, ← PrimeSpectrum.comap_asIdeal,
      IsAffineOpen.comap_primeIdealOf_appLE ⊤ (isAffineOpen_top _) V hV le_top hyV,
      comap_ΓSpecIso_inv_primeIdealOf_top, base_fst_asIdeal]
  haveI hR : Algebra.IsSmoothAt R q.asIdeal := Algebra.isSmoothAt_of_smooth_tensorProduct_field _ hq

  obtain ⟨g, hgq, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R q.asIdeal
  set W := X.basicOpen g with hWdef
  have hW : IsAffineOpen W := hV.basicOpen g
  have hyW : y ∈ W := by
    have h1 : hV.fromSpec (hV.primeIdealOf ⟨y, hyV⟩) = y := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
    rw [← h1]
    change hV.primeIdealOf ⟨y, hyV⟩ ∈ hV.fromSpec ⁻¹ᵁ (X.basicOpen g)
    rw [hV.fromSpec_preimage_basicOpen]
    exact hgq
  refine ⟨W, hyW, ?_⟩
  letI := algebraOfHom c W
  haveI : IsScalarTower R Γ(X, V) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq (fun r => ((restrictAlgHom c (X.basicOpen_le g)).commutes r).symm)
  haveI : IsLocalization.Away g Γ(X, W) := hV.isLocalization_basicOpen g
  haveI : Algebra.IsStandardSmooth R Γ(X, W) :=
    Algebra.IsStandardSmooth.of_algEquiv
      ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, W)).restrictScalars R)

  have hW' : IsAffineOpen ((fst c k) ⁻¹ᵁ W) := isAffineOpen_preimage_fst c k W hW
  have hzW : z ∈ (fst c k) ⁻¹ᵁ W := hyW
  letI := algebraOfHom (snd c k) ((fst c k) ⁻¹ᵁ W)
  obtain ⟨s, hs, H⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) (snd c k) hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨(fst c k) ⁻¹ᵁ W, hW'⟩ le_top
  set Q := hW'.primeIdealOf ⟨z, hzW⟩ with hQdef
  obtain ⟨t, hts, htQ⟩ : ∃ t ∈ s, t ∉ Q.asIdeal := by
    by_contra hall
    push Not at hall
    have : Ideal.span s ≤ Q.asIdeal := Ideal.span_le.mpr hall
    rw [hs, top_le_iff] at this
    exact Q.isPrime.ne_top this
  have Ht := H t hts

  haveI : Nontrivial (Localization.Away t) := by
    have hdisj : Disjoint (↑(Submonoid.powers t) : Set Γ(XA c k, (fst c k) ⁻¹ᵁ W)) ↑Q.asIdeal := by
      rw [Set.disjoint_left]
      rintro _ ⟨n, rfl⟩ hn
      exact htQ (Q.isPrime.mem_of_pow_mem n hn)
    have hP : (Ideal.map (algebraMap _ (Localization.Away t)) Q.asIdeal).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) _ Q.asIdeal Q.isPrime hdisj
    exact ⟨⟨0, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr (h ▸ Ideal.zero_mem _))⟩⟩

  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Localization.Away t) := by
    have h2 : (((algebraMap _ (Localization.Away t)).comp
        (Scheme.Hom.appLE (snd c k) ⊤ ((fst c k) ⁻¹ᵁ W) le_top).hom).comp
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.toRingHom).IsStandardSmoothOfRelativeDimension 1 :=
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ _ Ht
    have h3 : algebraMap k (Localization.Away t) = ((algebraMap _ (Localization.Away t)).comp
        (Scheme.Hom.appLE (snd c k) ⊤ ((fst c k) ⁻¹ᵁ W) le_top).hom).comp
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.toRingHom := by
      rw [IsScalarTower.algebraMap_eq k Γ(XA c k, (fst c k) ⁻¹ᵁ W) (Localization.Away t)]
      rfl
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap, h3]
    exact h2
  have h1 : Algebra.IsStandardSmoothOfRelativeDimension 1 R Γ(X, W) :=
    Algebra.isStandardSmoothOfRelativeDimension_of_baseChange_localization' (algEquiv c k W hW) t 1

  haveI : IsAffine W := hW
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension 1)]
  have e₁ : W ≤ c ⁻¹ᵁ ⊤ := le_top
  have key0 : (W.ι ≫ c).appTop ≫ W.topIso.hom = c.appLE ⊤ W e₁ := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, opens_ι_appTop_topIso_hom]
    rfl
  have key : (W.ι ≫ c).appTop = c.appLE ⊤ W e₁ ≫ W.topIso.inv := by
    rw [← key0, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hP0 : RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap R Γ(X, W)) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr h1
  have hP : RingHom.IsStandardSmoothOfRelativeDimension 1 (c.appLE ⊤ W e₁).hom := by
    have h2 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv hP0
    have h3 : (c.appLE ⊤ W e₁).hom = (algebraMap R Γ(X, W)).comp
        (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toRingHom := by
      change _ = (((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ W le_top).hom).comp (Scheme.ΓSpecIso (.of R)).hom.hom
      rw [← CommRingCat.hom_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h3]; exact h2
  have hQ' : RingHom.IsStandardSmoothOfRelativeDimension 1 ((W.ι ≫ c).appTop).hom := by
    rw [key, CommRingCat.hom_comp]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 (c.appLE ⊤ W e₁).hom
      W.topIso.symm.commRingCatIsoToRingEquiv hP
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hQ'

theorem exists_mem_and_smoothOfRelativeDimension_one_of_pullback_snd
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [Flat c] [LocallyOfFinitePresentation c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hsm : SmoothOfRelativeDimension 1 (pullback.snd c x)) :
    ∀ y ∈ Set.range (pullback.fst c x).base, ∃ W : C.Opens, y ∈ W ∧ SmoothOfRelativeDimension 1 (W.ι ≫ c) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  letI : Algebra R k := φ.hom.toAlgebra
  rintro y ⟨z, rfl⟩
  exact exists_mem_and_smoothOfRelativeDimension_one_of_snd c k hsm z

end AlgebraicGeometry.SmoothFibre
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.SmoothFibre"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.SmoothFibre"

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [Flat c] [LocallyOfFinitePresentation c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hsm : SmoothOfRelativeDimension 1 (pullback.snd c x)) :
    ∀ y ∈ Set.range (pullback.fst c x).base, ∃ W : C.Opens, y ∈ W ∧ SmoothOfRelativeDimension 1 (W.ι ≫ c) :=
  AlgebraicGeometry.SmoothFibre.exists_mem_and_smoothOfRelativeDimension_one_of_pullback_snd c x hsm

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd.AlgebraicGeometry.SmoothFibre"

end S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
end P2MW
export P2MW.S_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd (solution)
