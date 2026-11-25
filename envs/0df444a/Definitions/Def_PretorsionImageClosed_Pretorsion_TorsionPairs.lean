-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
-- name    : PretorsionImageClosed_Pretorsion_TorsionPairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T06:41:25.703436+00:00
-- url     : https://prove2.me/theorems/f8a4f7f1-b178-400e-984c-adbb22c6f8b2
-- title:
--   Torsion Pairs
-- statement:
--   Definitions and structural lemmas for Torsion Pairs, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/TorsionPairs.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory ZeroObject
variable {C : Type*} [Category C] [Abelian C]
def IsTorsionPair (T F : ObjectProperty C) : Prop :=
  (∀ {X Y : C} (f : X ⟶ Y), T X → F Y → f = 0) ∧
    ∀ X : C, ∃ (T' F' : C) (u : T' ⟶ X) (v : X ⟶ F') (w : u ≫ v = 0),
      T T' ∧ F F' ∧ (ShortComplex.mk u v w).ShortExact
variable [HasLength C]
namespace PretorsionTheory
def IsTorsion (P : PretorsionTheory C) : Prop := IsTorsionPair P.T.prop P.F.prop
end PretorsionTheory
end PretorsionImageClosed.Statement


