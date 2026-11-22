-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
-- name    : LeanPool_DeciSigma1_Holes_Tail_ClosedForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:58:12.086371+00:00
-- url     : https://prove2.me/theorems/4215d8bb-ab99-45f4-b06d-26e0e2ffc785
-- title:
--   Closed Form
-- statement:
--   Definitions and structural lemmas for Closed Form, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedForm.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open Arithmetic
def initialLogBound (k N : ℕ) : ℕ :=
  let Q := levelMultiplicity k N
  k + N + Q + N * N + k * N + k * (Q + 3) + 20
def levelLogSlope (k N : ℕ) : ℕ :=
  (k + N + 10) * (levelMultiplicity k N + N + 3) ^ k + 5
end DeciSigma1.Holes.Tail


