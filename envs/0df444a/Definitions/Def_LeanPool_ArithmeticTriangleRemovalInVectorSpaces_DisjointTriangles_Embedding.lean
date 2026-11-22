-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Embedding
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Embedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:12:33.37356+00:00
-- url     : https://prove2.me/theorems/0e2ce762-30dd-4164-9e9a-ca16a08c237e
-- title:
--   Embedding
-- statement:
--   Definitions and structural lemmas for Embedding, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/DisjointTriangles/Embedding.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Pruning
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Function Submodule
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {V : Type*}
def lift (p : ℕ) (a b : ZMod p) (x : V) : V × ZMod p × ZMod p :=
  (x, a, b)
variable [AddCommGroup V] {p : ℕ}
variable [Module (ZMod p) V]
variable [DecidableEq V] {X Y Z : Finset V}
section GeneralPosition
variable {a b c a' b' c' : V × ZMod p × ZMod p}
end GeneralPosition
variable [Fact p.Prime] [Fintype V] {ι : Type*} [Fintype ι] {x y z : ι → V}
end ArithmeticTriangleRemovalInVectorSpaces


