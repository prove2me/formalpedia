-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:37.202806+00:00
-- url     : https://prove2.me/theorems/d81bbf64-f10a-4c56-9514-ff470544196d
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Finset
namespace ArithmeticTriangleRemovalInVectorSpaces
def sumTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1)).filter fun (a, b, c) ↦ a + b + c = N
@[expose] def marginal (N : ℕ) (J : ℕ × ℕ × ℕ → ℝ) (g : ℕ × ℕ × ℕ → ℕ) (k : ℕ) : ℝ :=
  ∑ x ∈ sumTriples N with g x = k, J x
@[expose] def Compatible (N : ℕ) (π₁ π₂ π₃ : ℕ → ℝ) : Prop :=
  ∃ J : ℕ × ℕ × ℕ → ℝ, (∀ x, 0 ≤ J x) ∧ marginal N J (fun (a, _, _) ↦ a) = π₁ ∧
    marginal N J (fun (_, b, _) ↦ b) = π₂ ∧ marginal N J (fun (_, _, c) ↦ c) = π₃
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}
def shiftThird (d : ℕ) (J : ℕ × ℕ × ℕ → ℝ) : ℕ × ℕ × ℕ → ℝ :=
  fun (a, b, c) ↦ if d ≤ c then J (a, b, c - d) else 0
end ArithmeticTriangleRemovalInVectorSpaces


