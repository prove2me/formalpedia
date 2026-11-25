-- Prove2me | Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
-- name    : PretorsionImageClosed_ConvexGeometry_Compact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:51:30.036831+00:00
-- url     : https://prove2.me/theorems/2411f793-8933-4cac-883f-0015aad438c2
-- title:
--   Compact
-- statement:
--   Definitions and structural lemmas for Compact, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Compact.lean

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
namespace PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
def finiteClosuresBelow (c : SetClosure E) (C : c.Closeds) :
    Set c.Closeds :=
  {K | ∃ B : Set E, B.Finite ∧ B ⊆ (C : Set E) ∧
    K = c.toCloseds B}
end PretorsionImageClosed.SetClosure


