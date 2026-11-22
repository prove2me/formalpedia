-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decomposition
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:49.291241+00:00
-- url     : https://prove2.me/theorems/de3c807d-06e4-4ab8-bb5d-4f6849c28aa7
-- title:
--   Decomposition
-- statement:
--   Definitions and structural lemmas for Decomposition, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Decomposition.lean

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset Function
namespace ArithmeticTriangleRemovalInVectorSpaces
@[expose] def IsWeight (N : ℕ) (w : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ w k) ∧ ∀ k, N < k → w k = 0
@[expose] def IsBalanced (N : ℕ) (w₁ w₂ w₃ : ℕ → ℝ) : Prop :=
  IsWeight N w₁ ∧ IsWeight N w₂ ∧ IsWeight N w₃ ∧ mass N w₂ = mass N w₁ ∧
    mass N w₃ = mass N w₁ ∧ moment N w₁ + moment N w₂ + moment N w₃ = 2 * N * mass N w₁
def IsUnitBelow (N : ℕ) (w σ : ℕ → ℝ) (μ : ℝ) : Prop :=
  IsWeight N σ ∧ mass N σ = 1 ∧ moment N σ = μ ∧ support σ ⊆ support w
noncomputable def supportCard (N : ℕ) (w : ℕ → ℝ) : ℕ :=
  #{k ∈ range (N + 1) | w k ≠ 0}
variable {N : ℕ} {w w₁ w₂ w₃ σ σ₁ σ₂ σ₃ : ℕ → ℝ} {μ μ₁ μ₂ μ₃ p : ℝ}
end ArithmeticTriangleRemovalInVectorSpaces


