-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:46.474497+00:00
-- url     : https://prove2.me/theorems/22b8e416-2b16-4755-a926-514679e9a108
-- title:
--   Product
-- statement:
--   Definitions and structural lemmas for Product, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Abel
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Function
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {ι G W : Type*} [AddCommGroup G] [AddCommGroup W] {x y z : ι → G}
section Base
variable [DecidableEq G] [Fintype ι]
end Base
variable [DecidableEq G] [DecidableEq W] [Fintype ι] [Fintype W]
end ArithmeticTriangleRemovalInVectorSpaces


