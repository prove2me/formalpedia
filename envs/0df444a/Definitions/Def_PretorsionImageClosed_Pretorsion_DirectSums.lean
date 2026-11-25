-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_DirectSums
-- name    : PretorsionImageClosed_Pretorsion_DirectSums
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:05:18.302975+00:00
-- url     : https://prove2.me/theorems/e6356985-3449-4439-ab90-13287d2c3ae4
-- title:
--   Direct Sums
-- statement:
--   Definitions and structural lemmas for Direct Sums, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_comp_left
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_comp_right

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
namespace PretorsionImageClosed.Statement
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] {Zs : Subcategory C}
theorem biprod_map_comp_map {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : biprod.map f₁ f₂ ≫ biprod.map g₁ g₂ = biprod.map (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply biprod.hom_ext <;> simp
theorem IsTrivial.biprod_map {X₁ X₂ Y₁ Y₂ : C} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (h₁ : IsTrivial Zs.prop f₁) (h₂ : IsTrivial Zs.prop f₂) :
    IsTrivial Zs.prop (biprod.map f₁ f₂) := by
  obtain ⟨W₁, hW₁, g₁, k₁, rfl⟩ := h₁
  obtain ⟨W₂, hW₂, g₂, k₂, rfl⟩ := h₂
  exact ⟨W₁ ⊞ W₂, Zs.prop_biprod hW₁ hW₂, biprod.map g₁ g₂, biprod.map k₁ k₂,
    biprod_map_comp_map _ _ _ _⟩
theorem IsPrekernel.biprod {T₁ X₁ F₁ T₂ X₂ F₂ : C} {u₁ : T₁ ⟶ X₁} {v₁ : X₁ ⟶ F₁} {u₂ : T₂ ⟶ X₂}
    {v₂ : X₂ ⟶ F₂} (h₁ : IsPrekernel Zs.prop u₁ v₁) (h₂ : IsPrekernel Zs.prop u₂ v₂) :
    IsPrekernel Zs.prop (biprod.map u₁ u₂) (biprod.map v₁ v₂) := by
  refine ⟨?_, ?_⟩
  · rw [biprod_map_comp_map]
    exact h₁.1.biprod_map h₂.1
  · intro Y u' hu'
    have t₁ : IsTrivial Zs.prop ((u' ≫ biprod.fst) ≫ v₁) := by
      rw [Category.assoc, ← biprod.map_fst, ← Category.assoc]
      exact hu'.comp_right _
    have t₂ : IsTrivial Zs.prop ((u' ≫ biprod.snd) ≫ v₂) := by
      rw [Category.assoc, ← biprod.map_snd, ← Category.assoc]
      exact hu'.comp_right _
    obtain ⟨w₁, hw₁, hu₁⟩ := h₁.2 _ t₁
    obtain ⟨w₂, hw₂, hu₂⟩ := h₂.2 _ t₂
    refine ⟨biprod.lift w₁ w₂, ?_, ?_⟩
    · apply biprod.hom_ext <;> simp [hw₁, hw₂]
    · intro w hw
      apply biprod.hom_ext
      · rw [biprod.lift_fst]
        apply hu₁
        rw [Category.assoc, ← biprod.map_fst, ← Category.assoc, hw]
      · rw [biprod.lift_snd]
        apply hu₂
        rw [Category.assoc, ← biprod.map_snd, ← Category.assoc, hw]
theorem IsPrecokernel.biprod {T₁ X₁ F₁ T₂ X₂ F₂ : C} {u₁ : T₁ ⟶ X₁} {v₁ : X₁ ⟶ F₁} {u₂ : T₂ ⟶ X₂}
    {v₂ : X₂ ⟶ F₂} (h₁ : IsPrecokernel Zs.prop u₁ v₁) (h₂ : IsPrecokernel Zs.prop u₂ v₂) :
    IsPrecokernel Zs.prop (biprod.map u₁ u₂) (biprod.map v₁ v₂) := by
  refine ⟨?_, ?_⟩
  · rw [biprod_map_comp_map]
    exact h₁.1.biprod_map h₂.1
  · intro Y v' hv'
    have t₁ : IsTrivial Zs.prop (u₁ ≫ biprod.inl ≫ v') := by
      rw [← Category.assoc, ← biprod.inl_map, Category.assoc]
      exact hv'.comp_left _
    have t₂ : IsTrivial Zs.prop (u₂ ≫ biprod.inr ≫ v') := by
      rw [← Category.assoc, ← biprod.inr_map, Category.assoc]
      exact hv'.comp_left _
    obtain ⟨w₁, hw₁, hv₁⟩ := h₁.2 _ t₁
    obtain ⟨w₂, hw₂, hv₂⟩ := h₂.2 _ t₂
    refine ⟨biprod.desc w₁ w₂, ?_, ?_⟩
    · apply biprod.hom_ext' <;> simp [hw₁, hw₂]
    · intro w hw
      apply biprod.hom_ext'
      · rw [biprod.inl_desc]
        apply hv₁
        rw [← Category.assoc, ← biprod.inl_map, Category.assoc, hw]
      · rw [biprod.inr_desc]
        apply hv₂
        rw [← Category.assoc, ← biprod.inr_map, Category.assoc, hw]
end PretorsionImageClosed.Statement


