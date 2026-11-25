-- Prove2me | Definitions.Def_PretorsionImageClosed_Subcategories_Basic
-- name    : PretorsionImageClosed_Subcategories_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:40.98842+00:00
-- url     : https://prove2.me/theorems/f16171cf-090a-49ad-9476-5cc5b11ed7db
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
namespace Statement
section Trivial
variable {C : Type*} [Category C] {Z : ObjectProperty C}
end Trivial
end Statement
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
namespace Statement.Subcategory
variable (Z : Subcategory C)
@[ext]
theorem ext {Z Z' : Subcategory C} (h : Z.prop = Z'.prop) : Z = Z' := by
  cases Z; cases Z'; cases h; rfl
theorem prop_of_iso {X Y : C} (e : X ≅ Y) (hX : Z.prop X) : Z.prop Y :=
  Z.prop_of_retract (Retract.ofIso e.symm) hX
instance : Z.prop.IsClosedUnderIsomorphisms where
  of_iso e hX := Z.prop_of_iso e hX
instance : PartialOrder (Subcategory C) where
  le Z Z' := Z.prop ≤ Z'.prop
  le_refl _ := le_rfl
  le_trans _ _ _ h h' := h.trans h'
  le_antisymm _ _ h h' := ext (le_antisymm h h')
instance : Top (Subcategory C) where
  top := { prop := ⊤
           prop_of_retract := fun _ _ => trivial
           prop_biprod := fun _ _ => trivial
           prop_of_isZero := fun _ => trivial }
@[simp] theorem top_prop : (⊤ : Subcategory C).prop = ⊤ := rfl
instance : Bot (Subcategory C) where
  bot := { prop := fun X => IsZero X
           prop_of_retract := fun {X Y} h hY => by
             rw [IsZero.iff_id_eq_zero, ← h.retract, hY.eq_zero_of_tgt h.i, zero_comp]
           prop_biprod := fun {X Y} hX hY => by
             refine ⟨fun Z => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun Z => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
             · apply biprod.hom_ext'
               · rw [hX.eq_zero_of_src (biprod.inl ≫ f), hX.eq_zero_of_src (biprod.inl ≫ _)]
               · rw [hY.eq_zero_of_src (biprod.inr ≫ f), hY.eq_zero_of_src (biprod.inr ≫ _)]
             · apply biprod.hom_ext
               · rw [hX.eq_zero_of_tgt (f ≫ biprod.fst), hX.eq_zero_of_tgt (_ ≫ biprod.fst)]
               · rw [hY.eq_zero_of_tgt (f ≫ biprod.snd), hY.eq_zero_of_tgt (_ ≫ biprod.snd)]
           prop_of_isZero := fun h => h }
@[simp] theorem bot_prop : (⊥ : Subcategory C).prop = fun X => IsZero X := rfl
instance : Min (Subcategory C) where
  min Z Z' :=
    { prop := Z.prop ⊓ Z'.prop
      prop_of_retract := fun h hY => ⟨Z.prop_of_retract h hY.1, Z'.prop_of_retract h hY.2⟩
      prop_biprod := fun hX hY => ⟨Z.prop_biprod hX.1 hY.1, Z'.prop_biprod hX.2 hY.2⟩
      prop_of_isZero := fun h => ⟨Z.prop_of_isZero h, Z'.prop_of_isZero h⟩ }
@[simp] theorem inf_prop (Z Z' : Subcategory C) : (Z ⊓ Z').prop = Z.prop ⊓ Z'.prop := rfl
def iInf {ι : Sort*} (Z : ι → Subcategory C) : Subcategory C where
  prop := ⨅ i, (Z i).prop
  prop_of_retract h hY := by
    simp only [iInf_apply, iInf_Prop_eq] at hY ⊢
    exact fun i => (Z i).prop_of_retract h (hY i)
  prop_biprod hX hY := by
    simp only [iInf_apply, iInf_Prop_eq] at hX hY ⊢
    exact fun i => (Z i).prop_biprod (hX i) (hY i)
  prop_of_isZero h := by
    simp only [iInf_apply, iInf_Prop_eq]
    exact fun i => (Z i).prop_of_isZero h
@[simp] theorem iInf_prop {ι : Sort*} (Z : ι → Subcategory C) :
    (iInf Z).prop = ⨅ i, (Z i).prop := rfl
theorem iInf_prop_iff {ι : Sort*} (Z : ι → Subcategory C) (X : C) :
    (iInf Z).prop X ↔ ∀ i, (Z i).prop X := by
  simp [iInf_prop]
def IsQuotientClosed : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), Epi f → Z.prop X → Z.prop Y
def IsSubobjectClosed : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), Mono f → Z.prop Y → Z.prop X
theorem IsQuotientClosed.iInf {ι : Sort*} {Z : ι → Subcategory C}
    (h : ∀ i, (Z i).IsQuotientClosed) : (Subcategory.iInf Z).IsQuotientClosed := by
  intro X Y f hf hX
  rw [iInf_prop_iff] at hX ⊢
  exact fun i => h i f hf (hX i)
theorem IsSubobjectClosed.iInf {ι : Sort*} {Z : ι → Subcategory C}
    (h : ∀ i, (Z i).IsSubobjectClosed) : (Subcategory.iInf Z).IsSubobjectClosed := by
  intro X Y f hf hY
  rw [iInf_prop_iff] at hY ⊢
  exact fun i => h i f hf (hY i)
end Statement.Subcategory
section Abelian
variable {A : Type*} [Category A] [Abelian A]
namespace Statement.Subcategory
variable (Z : Subcategory A)
abbrev IsImageClosed : Prop := Statement.IsImageClosed Z.prop
end Statement.Subcategory
end Abelian
namespace Statement
end Statement
end PretorsionImageClosed


