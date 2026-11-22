-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:36.120013+00:00
-- url     : https://prove2.me/theorems/791056cf-9ca7-4c90-b7cd-7ab6e52504a1
-- title:
--   Exponent
-- statement:
--   Definitions and structural lemmas for Exponent, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Exponent.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Filter Topology
namespace ArithmeticTriangleRemovalInVectorSpaces
noncomputable def c (p : ℕ) : ℝ :=
  1 - Real.logb p
    (⨅ x : Set.Ioo (0 : ℝ) 1, (x : ℝ) ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, (x : ℝ) ^ j)
noncomputable def C (p : ℕ) : ℝ :=
  1 + 1 / c p
noncomputable def n₀ (p : ℕ) (η : ℝ) : ℕ :=
  ⌈(2 ^ (p + 3) * p ^ 10 / η) ^ 2⌉₊ + p ^ 4 + 1
noncomputable def ε₀ (p : ℕ) (η : ℝ) : ℝ :=
  ((p : ℝ) ^ (n₀ p (c p * min (1 - c p) (c p * η / 2) / 2) + 1))⁻¹
variable {p : ℕ}
end ArithmeticTriangleRemovalInVectorSpaces


