-- Prove2me | Definitions.Def_ChapterFiniteArithmeticPrior
-- name    : ChapterFiniteArithmeticPrior
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:55:15.363654+00:00
-- url     : https://prove2.me/theorems/bb8e5677-4a0d-4b33-b04d-47ab4de9bab6
-- title:
--   Chapter FiniteArithmeticPrior
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFiniteArithmeticPrior.lean`): generated def bundle for ChapterFiniteArithmeticPrior. See BookProof/ChapterFiniteArithmeticPrior.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFiniteArithmeticPrior.lean

import Mathlib


/-!
# Finite arithmetic with a Bayesian prior beyond the truncation

This module gives a precise finite model of the book's proposal.  Arithmetic
results inside a bound `B` are stored exactly; results outside the finite table
are represented by a normalized nonnegative prior on a finite hypothesis space.
-/

namespace BookProof.ChapterFiniteArithmeticPrior

/-- A finite table for a binary arithmetic operation below a bound. -/
structure BoundedArithmetic (B : ℕ) where
  result : Fin B → Fin B → Fin B

/-- A Bayesian extension of bounded arithmetic by a finite hypothesis space. -/
structure BayesianArithmeticExtension (B : ℕ) (H : Type*) [Fintype H] where
  known : BoundedArithmetic B
  prior : H → ℝ
  prior_nonneg : ∀ h, 0 ≤ prior h
  prior_sum_one : ∑ h, prior h = 1



/-- Every exact bounded arithmetic table admits the degenerate one-hypothesis
Bayesian extension. -/
def certainExtension {B : ℕ} (A : BoundedArithmetic B) :
    BayesianArithmeticExtension B PUnit where
  known := A
  prior := fun _ => 1
  prior_nonneg := by intro; norm_num
  prior_sum_one := by simp



/-- The **truncated multiplication table** below the bound `B`: the exact product
whenever it still fits below `B`, and the largest representable value `B - 1`
otherwise.  This is the finite computation the book proposes to carry out
exactly, with everything beyond the truncation handled by a prior. -/
def truncMul (B : ℕ) [NeZero B] : BoundedArithmetic B where
  result a b :=
    if h : (a : ℕ) * (b : ℕ) < B then ⟨(a : ℕ) * (b : ℕ), h⟩
    else ⟨B - 1, Nat.sub_lt (Nat.pos_of_neZero B) Nat.one_pos⟩







end BookProof.ChapterFiniteArithmeticPrior


