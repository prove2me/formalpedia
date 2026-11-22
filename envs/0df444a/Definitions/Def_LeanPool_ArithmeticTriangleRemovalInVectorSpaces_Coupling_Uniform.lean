-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:27.896348+00:00
-- url     : https://prove2.me/theorems/8bea518d-effd-46e7-9fc5-6221fedf9be1
-- title:
--   Uniform
-- statement:
--   Definitions and structural lemmas for Uniform, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
@[expose] noncomputable def unif (k j : ℕ) : ℝ :=
  if j ≤ k then ((k : ℝ) + 1)⁻¹ else 0
@[expose] noncomputable def hat (N : ℕ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ range (N + 1), w k * unif k j
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}
end ArithmeticTriangleRemovalInVectorSpaces


