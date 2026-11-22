-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:34.15462+00:00
-- url     : https://prove2.me/theorems/c02722e3-020c-437d-9733-7b25d1a67520
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Basic.lean

module
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {ι G H : Type*} [AddCommGroup G] [AddCommGroup H]
def IsMulticoloredSumFree (x y z : ι → G) : Prop :=
  ∀ i j k, x i + y j + z k = 0 ↔ i = j ∧ j = k
namespace IsMulticoloredSumFree
variable {x y z : ι → G}
end IsMulticoloredSumFree
end ArithmeticTriangleRemovalInVectorSpaces


