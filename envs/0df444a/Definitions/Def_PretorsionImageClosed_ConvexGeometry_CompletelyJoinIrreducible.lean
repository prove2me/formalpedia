-- Prove2me | Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
-- name    : PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:49:19.16381+00:00
-- url     : https://prove2.me/theorems/20567953-b1a9-4b4e-81ca-27f2cbfce1d4
-- title:
--   Completely Join Irreducible
-- statement:
--   Definitions and structural lemmas for Completely Join Irreducible, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/CompletelyJoinIrreducible.lean

module
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
namespace PretorsionImageClosed
def IsCompletelyJoinIrreducible {L : Type*} [CompleteLattice L] (j : L) : Prop :=
  ∀ S : Set L, sSup S = j → j ∈ S
def IsSpatial (L : Type*) [CompleteLattice L] : Prop :=
  ∀ a : L, sSup {j : L | IsCompletelyJoinIrreducible j ∧ j ≤ a} = a
namespace SetClosure
variable {E : Type*} {c : SetClosure E}
end SetClosure
end PretorsionImageClosed


