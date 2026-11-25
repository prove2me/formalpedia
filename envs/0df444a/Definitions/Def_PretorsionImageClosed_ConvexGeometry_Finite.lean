-- Prove2me | Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
-- name    : PretorsionImageClosed_ConvexGeometry_Finite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:33.449899+00:00
-- url     : https://prove2.me/theorems/156762b1-c70f-4e4e-b4e8-de3bbe67e0ae
-- title:
--   Finite
-- statement:
--   Definitions and structural lemmas for Finite, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
namespace PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
def IsMinimalGenerator (c : SetClosure E) (B C : Set E) : Prop :=
  c B = C ∧ ∀ ⦃b : E⦄, b ∈ B → c (B \ {b}) ≠ C
end PretorsionImageClosed.SetClosure


