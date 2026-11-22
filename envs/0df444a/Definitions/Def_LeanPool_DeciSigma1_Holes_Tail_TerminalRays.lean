-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
-- name    : LeanPool_DeciSigma1_Holes_Tail_TerminalRays
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:53:40.514797+00:00
-- url     : https://prove2.me/theorems/632095e9-cf94-48e6-be26-6c1dbc40b03c
-- title:
--   Terminal Rays
-- statement:
--   Definitions and structural lemmas for Terminal Rays, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
def RayAgrees (Ω : Ray α) (x : List α) (E : ℕ) : Prop :=
  E ≤ x.length ∧ streamPrefix Ω.stream E = x.take E
section TerminalRay
variable {σ : ℕ} [DecidableEq α] [Fintype S]
end TerminalRay
section Original
variable [DecidableEq α] [DecidableEq S]
end Original
end DeciSigma1.Holes.Tail


