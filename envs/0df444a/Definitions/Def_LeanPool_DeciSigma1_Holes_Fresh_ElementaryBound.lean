-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
-- name    : LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:44:30.220191+00:00
-- url     : https://prove2.me/theorems/447ce499-5fac-4513-8996-6ea7fb6af983
-- title:
--   Elementary Bound
-- statement:
--   Definitions and structural lemmas for Elementary Bound, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/ElementaryBound.lean

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Fresh
open Arithmetic
def arithmeticBudget (k n : ℕ) : ℕ :=
  k * (k * n + 1) + n * n + 7 * k * n + k + 12
end DeciSigma1.Holes.Fresh


