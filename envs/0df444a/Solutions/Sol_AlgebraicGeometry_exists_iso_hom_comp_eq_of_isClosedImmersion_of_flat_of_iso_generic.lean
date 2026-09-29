-- Prove2me | solution 1 for AlgebraicGeometry.exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9a4851a5-b28b-5810-bfd5-a371a7bcfe1f

import Mathlib
import Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ClosureUniqAux

variable {R : Type} [CommRing R] (K : Type) [Field K] [Algebra R K]

noncomputable def genericToSpecTensor (A : Type) [CommRing A] [Algebra R A] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
      Spec (CommRingCat.of (K ⊗[R] A)) :=
  (pullbackSpecIso R A K).hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm R K A).toRingHom)

theorem genericToSpecTensor_comp_includeRight (A : Type) [CommRing A] [Algebra R A] :
    genericToSpecTensor K A ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A →+* K ⊗[R] A)) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  rw [genericToSpecTensor, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : ((Algebra.TensorProduct.comm R K A).toRingHom).comp
      (Algebra.TensorProduct.includeRight.toRingHom : A →+* K ⊗[R] A) =
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] K) := by
    ext a
    simp [Algebra.TensorProduct.includeLeftRingHom]
  rw [h]
  exact pullbackSpecIso_hom_fst R A K

end ClosureUniqAux

open ClosureUniqAux

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type} [CommRing R] [IsDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R))
    (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]
    [Module.Flat R A₁] [Module.Flat R A₂]
    (i₁ : Spec (CommRingCat.of A₁) ⟶ Y) (i₂ : Spec (CommRingCat.of A₂) ⟶ Y)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₁)))
    (h₂ : i₂ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₂)))
    (eK : Spec (CommRingCat.of (K ⊗[R] A₁)) ≅ Spec (CommRingCat.of (K ⊗[R] A₂)))
    (heK : eK.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₂ →+* K ⊗[R] A₂)) ≫ i₂ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i₁) :
    ∃ e : Spec (CommRingCat.of A₁) ≅ Spec (CommRingCat.of A₂), e.hom ≫ i₂ = i₁ := by

  haveI hF₁ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A₁))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI hF₂ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A₂))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

  have heK' : eK.inv ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i₁ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₂ →+* K ⊗[R] A₂)) ≫ i₂ := by
    rw [Iso.inv_comp_eq, heK]

  obtain ⟨ψ₁, hψ₁, -⟩ :=
    AlgebraicGeometry.existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq K
      (Spec.map (CommRingCat.ofHom (algebraMap R A₁))) i₂ i₁
      (genericToSpecTensor K A₁ ≫ eK.hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₂ →+* K ⊗[R] A₂)))
      (by rw [Category.assoc, Category.assoc, heK, ← Category.assoc, genericToSpecTensor_comp_includeRight])

  obtain ⟨ψ₂, hψ₂, -⟩ :=
    AlgebraicGeometry.existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq K
      (Spec.map (CommRingCat.ofHom (algebraMap R A₂))) i₁ i₂
      (genericToSpecTensor K A₂ ≫ eK.inv ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)))
      (by rw [Category.assoc, Category.assoc, heK', ← Category.assoc, genericToSpecTensor_comp_includeRight])

  have h12 : ψ₁ ≫ ψ₂ = 𝟙 _ := by
    rw [← cancel_mono i₁, Category.assoc, hψ₂, hψ₁, Category.id_comp]
  have h21 : ψ₂ ≫ ψ₁ = 𝟙 _ := by
    rw [← cancel_mono i₂, Category.assoc, hψ₁, hψ₂, Category.id_comp]
  exact ⟨⟨ψ₁, ψ₂, h12, h21⟩, hψ₁⟩

end S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic
end P2MW
export P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic (solution)
