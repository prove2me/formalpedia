-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Sampling
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Sampling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:11:11.648119+00:00
-- url     : https://prove2.me/theorems/3c4e585e-4281-43c5-ae65-76d15aaa3055
-- title:
--   Sampling
-- statement:
--   Definitions and structural lemmas for Sampling, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/DisjointTriangles/Sampling.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LinearMap_Card
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Module Submodule
namespace ArithmeticTriangleRemovalInVectorSpaces
section Good
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
def adjacentTriangles (X Y Z : Finset G) (x y z : G) : Finset (G × G × G) :=
  (triangles X Y Z).filter fun (x', y', z') ↦ (x' = x ∨ y' = y ∨ z' = z) ∧ (x', y', z') ≠ (x, y, z)
def goodTriangles (X Y Z : Finset G) : Finset (G × G × G) :=
  (triangles X Y Z).filter fun (x, y, z) ↦ adjacentTriangles X Y Z x y z = ∅
variable {X Y Z X' Y' Z' : Finset G} {x y z x' y' z' : G}
end Good
variable {p : ℕ} [Fact p.Prime] {V W ι : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  [DecidableEq V] [AddCommGroup W] [Module (ZMod p) W] [Fintype W] [DecidableEq W]
  {X Y Z : Finset V} {x y z x' y' z' : V}
section Count
variable [Fintype (V →ₗ[ZMod p] W)]
end Count
end ArithmeticTriangleRemovalInVectorSpaces


