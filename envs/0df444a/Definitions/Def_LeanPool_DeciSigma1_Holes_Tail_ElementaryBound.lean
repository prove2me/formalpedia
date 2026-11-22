-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ElementaryBound
-- name    : LeanPool_DeciSigma1_Holes_Tail_ElementaryBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:57:27.596241+00:00
-- url     : https://prove2.me/theorems/98ef4e9c-795e-4928-98a7-011f3d856e1c
-- title:
--   Elementary Bound
-- statement:
--   Definitions and structural lemmas for Elementary Bound, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ElementaryBound.lean

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open Arithmetic
def compressionSlope (k N D : ℕ) : ℕ :=
  2 ^ (k * (N - 1)) * (Periodic.comparisonGap N D + Periodic.statePeriodModulus N D)
def compressionIntercept (k N D r : ℕ) : ℕ :=
  Periodic.fixedMargin N D + Periodic.statePeriodModulus N D +
    ((2 * r + 1) * 2 ^ (k * (N - 1)) - 1) *
      (Periodic.comparisonGap N D + Periodic.statePeriodModulus N D)
def arithmeticBudget (k N D : ℕ) : ℕ := k * N + N * N + N + D + 4
end DeciSigma1.Holes.Tail


