-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
-- name    : LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:54:03.406144+00:00
-- url     : https://prove2.me/theorems/d12ad816-5e4c-4402-8700-0c11d8b4795b
-- title:
--   Level Elementary Bound
-- statement:
--   Definitions and structural lemmas for Level Elementary Bound, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/LevelElementaryBound.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open Arithmetic
def stateEnvelope (H : ℕ) (st : LevelState) : Prop :=
  st.periodBound ≤ exp2 H ∧ st.chainLengthBound ≤ exp2 H ∧
  st.previousChainLengthBound ≤ exp2 H ∧ st.terminalLengthBound ≤ exp2 H ∧
  st.uncoveredBound ≤ exp2 H
end DeciSigma1.Holes.Tail


