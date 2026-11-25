-- Prove2me | Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
-- name    : PretorsionImageClosed_Subobjects_Preimage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:03.31022+00:00
-- url     : https://prove2.me/theorems/bdb37159-89e4-463a-862d-dc08d480ace0
-- title:
--   Preimage
-- statement:
--   Definitions and structural lemmas for Preimage, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
theorem imageSubobject_eq_kernelSubobject_cokernel_π {X Y : C} (f : X ⟶ Y) :
    imageSubobject f = kernelSubobject (cokernel.π f) :=
  (ShortComplex.exact_iff_image_eq_kernel _).1 (ShortComplex.exact_cokernel f)
theorem kernelSubobject_cokernel_π_arrow {X : C} (L : Subobject X) :
    kernelSubobject (cokernel.π L.arrow) = L := by
  rw [← imageSubobject_eq_kernelSubobject_cokernel_π, imageSubobject_mono, Subobject.mk_arrow]
theorem Subobject.le_kernelSubobject_iff {X Y : C} (g : X ⟶ Y) (S : Subobject X) :
    S ≤ kernelSubobject g ↔ S.arrow ≫ g = 0 :=
  ⟨fun h => by rw [← Subobject.ofLE_arrow h, Category.assoc, kernelSubobject_arrow_comp, comp_zero],
   fun h => le_kernelSubobject _ _ h⟩
def Subobject.isoOfEq' {X : C} {S S' : Subobject X} (h : S = S') : (S : C) ≅ (S' : C) where
  hom := Subobject.ofLE S S' h.le
  inv := Subobject.ofLE S' S h.ge
  hom_inv_id := by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl]
  inv_hom_id := by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl]
@[reassoc (attr := simp)]
theorem Subobject.isoOfEq'_hom_arrow {X : C} {S S' : Subobject X} (h : S = S') :
    (Subobject.isoOfEq' h).hom ≫ S'.arrow = S.arrow :=
  Subobject.ofLE_arrow _
theorem Subobject.mk_comp_arrow_le {X : C} (S : Subobject X) (K : Subobject (S : C)) :
    Subobject.mk (K.arrow ≫ S.arrow) ≤ S :=
  Subobject.mk_le_of_comm K.arrow rfl
abbrev Subobject.preimage {X Y : C} (p : X ⟶ Y) (U : Subobject Y) : Subobject X :=
  kernelSubobject (p ≫ cokernel.π U.arrow)
theorem Subobject.le_preimage_iff {X Y : C} (p : X ⟶ Y) (U : Subobject Y) (S : Subobject X) :
    S ≤ Subobject.preimage p U ↔ U.Factors (S.arrow ≫ p) := by
  rw [Subobject.le_kernelSubobject_iff, ← Category.assoc,
    ← kernelSubobject_factors_iff, kernelSubobject_cokernel_π_arrow]
theorem Subobject.preimage_arrow_comp_factors {X Y : C} (p : X ⟶ Y) (U : Subobject Y) :
    U.Factors ((Subobject.preimage p U).arrow ≫ p) :=
  (Subobject.le_preimage_iff p U _).1 le_rfl
def Subobject.preimageToSubobject {X Y : C} (p : X ⟶ Y) (U : Subobject Y) :
    (Subobject.preimage p U : C) ⟶ (U : C) :=
  U.factorThru _ (Subobject.preimage_arrow_comp_factors p U)
@[reassoc (attr := simp)]
theorem Subobject.preimageToSubobject_arrow {X Y : C} (p : X ⟶ Y) (U : Subobject Y) :
    Subobject.preimageToSubobject p U ≫ U.arrow = (Subobject.preimage p U).arrow ≫ p :=
  Subobject.factorThru_arrow _ _ _
theorem Subobject.le_imageSubobject_preimage_arrow_comp {X Y : C} (p : X ⟶ Y) [Epi p]
    (U : Subobject Y) : U ≤ imageSubobject ((Subobject.preimage p U).arrow ≫ p) := by
  rw [imageSubobject_eq_kernelSubobject_cokernel_π, Subobject.le_kernelSubobject_iff]
  have hker : kernel.ι (p ≫ cokernel.π U.arrow) ≫
      (p ≫ cokernel.π ((Subobject.preimage p U).arrow ≫ p)) = 0 := by
    rw [← kernelSubobject_arrow' (p ≫ cokernel.π U.arrow), Category.assoc,
      ← Category.assoc (kernelSubobject (p ≫ cokernel.π U.arrow)).arrow, cokernel.condition,
      comp_zero]
  have hdesc := Abelian.comp_epiDesc (p ≫ cokernel.π U.arrow) _ hker
  have hc : cokernel.π U.arrow ≫ Abelian.epiDesc (p ≫ cokernel.π U.arrow) _ hker =
      cokernel.π ((Subobject.preimage p U).arrow ≫ p) := by
    rw [← cancel_epi p, ← Category.assoc]
    exact hdesc
  rw [← hc, ← Category.assoc, cokernel.condition, zero_comp]
theorem Subobject.imageSubobject_preimage_arrow_comp {X Y : C} (p : X ⟶ Y) [Epi p]
    (U : Subobject Y) : imageSubobject ((Subobject.preimage p U).arrow ≫ p) = U :=
  le_antisymm (imageSubobject_le _ _ (Subobject.preimageToSubobject_arrow p U))
    (Subobject.le_imageSubobject_preimage_arrow_comp p U)
instance Subobject.epi_preimageToSubobject {X Y : C} (p : X ⟶ Y) [Epi p] (U : Subobject Y) :
    Epi (Subobject.preimageToSubobject p U) := by
  have heq : Subobject.preimageToSubobject p U =
      factorThruImageSubobject ((Subobject.preimage p U).arrow ≫ p) ≫
        (Subobject.isoOfEq' (Subobject.imageSubobject_preimage_arrow_comp p U)).hom := by
    rw [← cancel_mono U.arrow, Category.assoc, Subobject.isoOfEq'_hom_arrow,
      imageSubobject_arrow_comp, Subobject.preimageToSubobject_arrow]
  rw [heq]
  exact epi_comp _ _
abbrev Subobject.push {C : Type*} [Category C] {X : C} (S : Subobject X) (K : Subobject (S : C)) :
    Subobject X :=
  Subobject.mk (K.arrow ≫ S.arrow)
section Push
variable {C : Type*} [Category C] [Abelian C] {X : C} (S : Subobject X) (K : Subobject (S : C))
theorem Subobject.push_le : Subobject.push S K ≤ S :=
  Subobject.mk_le_of_comm K.arrow rfl
end Push
end PretorsionImageClosed


