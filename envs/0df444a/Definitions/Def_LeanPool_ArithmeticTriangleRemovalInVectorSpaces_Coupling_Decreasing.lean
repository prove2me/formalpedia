-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decreasing
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decreasing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:11:25.096169+00:00
-- url     : https://prove2.me/theorems/ef5b4524-ac7c-42f5-bb0d-6a084e2abef9
-- title:
--   Decreasing
-- statement:
--   Definitions and structural lemmas for Decreasing, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Decreasing.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decomposition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {π π₁ π₂ π₃ : ℕ → ℝ}
@[expose] noncomputable def geom (N : ℕ) (ρ : ℝ) (k : ℕ) : ℝ :=
  if k ≤ N then ρ ^ k else 0
end ArithmeticTriangleRemovalInVectorSpaces


