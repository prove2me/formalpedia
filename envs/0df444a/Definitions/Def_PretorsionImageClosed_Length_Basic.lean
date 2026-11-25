-- Prove2me | Definitions.Def_PretorsionImageClosed_Length_Basic
-- name    : PretorsionImageClosed_Length_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:04.018806+00:00
-- url     : https://prove2.me/theorems/18716529-3d22-4870-a406-7a44fa25a9b6
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Basic.lean

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
class HasLength (C : Type*) [Category C] [HasZeroMorphisms C] where
  /-- The length of an object. -/
  length : C → ℕ
  length_eq_zero_iff : ∀ X : C, length X = 0 ↔ IsZero X
  length_eq_of_iso : ∀ {X Y : C}, (X ≅ Y) → length X = length Y
  length_lt_of_mono : ∀ {X Y : C} (f : X ⟶ Y), Mono f → ¬ IsIso f → length X < length Y
  length_lt_of_epi : ∀ {X Y : C} (f : X ⟶ Y), Epi f → ¬ IsIso f → length Y < length X
export HasLength (length)
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasLength C]
section Subobject
variable {X : C} (S : Subobject X)
end Subobject
end PretorsionImageClosed


