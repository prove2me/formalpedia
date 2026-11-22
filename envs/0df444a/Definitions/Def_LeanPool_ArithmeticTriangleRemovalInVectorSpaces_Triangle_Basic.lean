-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:34.204799+00:00
-- url     : https://prove2.me/theorems/46c09e5a-db09-43fa-a3ea-d03d2c129f50
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Triangle/Basic.lean

module
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
def triangles (X Y Z : Finset G) : Finset (G × G × G) :=
  (X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0
variable {X Y Z X' Y' Z' : Finset G} {x y z : G}
end ArithmeticTriangleRemovalInVectorSpaces


