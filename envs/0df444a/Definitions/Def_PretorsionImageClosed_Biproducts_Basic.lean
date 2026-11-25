-- Prove2me | Definitions.Def_PretorsionImageClosed_Biproducts_Basic
-- name    : PretorsionImageClosed_Biproducts_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:06.037586+00:00
-- url     : https://prove2.me/theorems/374a70e1-116c-4b54-8eb0-44702042dd52
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Biproducts/Basic.lean

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
def isoBiprodCokernelOfIsSplitMono {C : Type*} [Category C] [Abelian C] {A X : C} (f : A ⟶ X)
    [IsSplitMono f] : X ≅ A ⊞ cokernel f :=
  biprod.uniqueUpToIso A (cokernel f)
    (isBilimitBinaryBiconeOfIsSplitMonoOfCokernel (cokernelIsCokernel f))
section FinSucc
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
theorem comp_biprod_lift {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : X ⟶ Z) :
    f ≫ biprod.lift g h = biprod.lift (f ≫ g) (f ≫ h) := by
  apply biprod.hom_ext <;> simp
theorem ι_zero_comp_lift_succ {n : ℕ} (f : Fin (n + 1) → C) :
    biproduct.ι f 0 ≫ biproduct.lift (fun (j : Fin n) => biproduct.π f j.succ) = 0 := by
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc, biproduct.lift_π, zero_comp, biproduct.ι_π_ne _ (Fin.succ_ne_zero j).symm]
theorem ι_succ_comp_lift_succ {n : ℕ} (f : Fin (n + 1) → C) (i : Fin n) :
    biproduct.ι f i.succ ≫ biproduct.lift (fun (j : Fin n) => biproduct.π f j.succ) =
      biproduct.ι (fun (j : Fin n) => f j.succ) i := by
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc, biproduct.lift_π]
  by_cases h : i = j
  · subst h
    rw [biproduct.ι_π_self, biproduct.ι_π_self]
  · rw [biproduct.ι_π_ne _ (fun h' => h (Fin.succ_injective _ h')), biproduct.ι_π_ne _ h]
def biproductFinSuccIso {n : ℕ} (f : Fin (n + 1) → C) :
    ⨁ f ≅ f 0 ⊞ ⨁ (fun j : Fin n => f j.succ) where
  hom := biprod.lift (biproduct.π f 0) (biproduct.lift fun (j : Fin n) => biproduct.π f j.succ)
  inv := biprod.desc (biproduct.ι f 0) (biproduct.desc fun (j : Fin n) => biproduct.ι f j.succ)
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [← Category.assoc, comp_biprod_lift, biproduct.ι_π_self, ι_zero_comp_lift_succ,
        Category.comp_id]
      have : biprod.lift (𝟙 (f 0)) (0 : f 0 ⟶ ⨁ fun (j : Fin n) => f j.succ) = biprod.inl := by
        apply biprod.hom_ext <;> simp
      rw [this, biprod.inl_desc]
    · rw [← Category.assoc, comp_biprod_lift, biproduct.ι_π_ne _ (Fin.succ_ne_zero i),
        ι_succ_comp_lift_succ, Category.comp_id]
      have : biprod.lift (0 : f i.succ ⟶ f 0) (biproduct.ι (fun (j : Fin n) => f j.succ) i) =
          biproduct.ι (fun (j : Fin n) => f j.succ) i ≫ biprod.inr := by
        apply biprod.hom_ext <;> simp
      rw [this, Category.assoc, biprod.inr_desc, biproduct.ι_desc]
  inv_hom_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, comp_biprod_lift, biproduct.ι_π_self, ι_zero_comp_lift_succ,
        Category.comp_id]
      apply biprod.hom_ext <;> simp
    · apply biproduct.hom_ext'
      intro i
      rw [biprod.inr_desc_assoc, biproduct.ι_desc_assoc, comp_biprod_lift,
        biproduct.ι_π_ne _ (Fin.succ_ne_zero i), ι_succ_comp_lift_succ, Category.comp_id]
      apply biprod.hom_ext <;> simp
end FinSucc
end PretorsionImageClosed


