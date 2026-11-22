-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
-- name    : LeanPool_DeciSigma1_Holes_Tail_WindowChains
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:53:50.154722+00:00
-- url     : https://prove2.me/theorems/10763c1a-651c-4041-9dc9-2745c9e0e779
-- title:
--   Window Chains
-- statement:
--   Definitions and structural lemmas for Window Chains, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
section Occurrences
variable [DecidableEq α]
end Occurrences
section Chains
variable {σ : ℕ} [DecidableEq α] [Fintype S] [DecidableEq S]
end Chains
end DeciSigma1.Holes.Tail


