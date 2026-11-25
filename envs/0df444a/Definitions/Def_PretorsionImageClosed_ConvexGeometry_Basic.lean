-- Prove2me | Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
-- name    : PretorsionImageClosed_ConvexGeometry_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:03.822892+00:00
-- url     : https://prove2.me/theorems/22cd2629-c0e0-492b-9c72-fdc773c168a0
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean

module
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.Closure
public import Mathlib.Order.Preorder.Finite
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
namespace PretorsionImageClosed
abbrev SetClosure (E : Type*) := ClosureOperator (Set E)
namespace SetClosure
variable {E : Type*} (c : SetClosure E)
def IsFinitary : Prop :=
  ∀ ⦃X : Set E⦄ ⦃x : E⦄, x ∈ c X →
    ∃ Y : Set E, Y.Finite ∧ Y ⊆ X ∧ x ∈ c Y
def IsAntiExchange : Prop :=
  ∀ ⦃C : Set E⦄ ⦃x y : E⦄, c.IsClosed C → x ∉ C → y ∉ C → x ≠ y →
    x ∈ c (insert y C) → y ∉ c (insert x C)
def IsConvexGeometry : Prop :=
  c.IsClosed ∅ ∧ c.IsAntiExchange
def extremePoints (C : Set E) : Set E :=
  {x | x ∈ C ∧ x ∉ c (C \ {x})}
variable {c}
end SetClosure
end PretorsionImageClosed


