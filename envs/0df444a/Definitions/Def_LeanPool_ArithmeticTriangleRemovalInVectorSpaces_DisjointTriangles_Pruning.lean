-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Pruning
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Pruning
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:11:50.708922+00:00
-- url     : https://prove2.me/theorems/0f8a0e3c-acc9-44eb-ad7a-e2d6a68239f6
-- title:
--   Pruning
-- statement:
--   Definitions and structural lemmas for Pruning, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/DisjointTriangles/Pruning.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Sampling
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Function Submodule
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {V ι : Type*} [AddCommGroup V] [DecidableEq V] [Fintype ι] {x y z : ι → V}
noncomputable def potential (x y z : ι → V) (A η : ℝ) : Finset V × Finset V × Finset V → ℝ
  | (X, Y, Z) => #{i | ¬(x i ∈ X ∧ y i ∈ Y ∧ z i ∈ Z)} + A * #(triangles X Y Z) ^ η
variable {A η : ℝ} {X Y Z X' Y' Z' : Finset V} {v : V}
variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Fintype V]
end ArithmeticTriangleRemovalInVectorSpaces


