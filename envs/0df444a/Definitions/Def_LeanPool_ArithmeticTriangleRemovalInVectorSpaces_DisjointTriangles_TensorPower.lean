-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_TensorPower
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_TensorPower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:12:59.741381+00:00
-- url     : https://prove2.me/theorems/1b7134b2-e45f-439e-ac8a-08087ac861d0
-- title:
--   Tensor Power
-- statement:
--   Definitions and structural lemmas for Tensor Power, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/DisjointTriangles/TensorPower.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Embedding
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Pruning
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Function
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime] {V ι : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  [DecidableEq V] [Fintype ι] {x y z : ι → V} {X Y Z : Finset V}
end ArithmeticTriangleRemovalInVectorSpaces


