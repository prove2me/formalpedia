-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_MaximalFamily
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_MaximalFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:13:40.785801+00:00
-- url     : https://prove2.me/theorems/0b29b683-8bf0-4f0d-8f63-83104cedaa4d
-- title:
--   Maximal Family
-- statement:
--   Definitions and structural lemmas for Maximal Family, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/DisjointTriangles/MaximalFamily.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_TensorPower
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Function
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {V : Type*}
def IsVertexDisjoint (S : Finset (V × V × V)) : Prop :=
  Set.InjOn (fun ((x, _, _) : V × V × V) ↦ x) S ∧
    Set.InjOn (fun ((_, y, _) : V × V × V) ↦ y) S ∧ Set.InjOn (fun ((_, _, z) : V × V × V) ↦ z) S
variable [DecidableEq V] {S : Finset (V × V × V)} {x y z : V}
variable [AddCommGroup V] {X Y Z : Finset V}
variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Fintype V]
end ArithmeticTriangleRemovalInVectorSpaces


