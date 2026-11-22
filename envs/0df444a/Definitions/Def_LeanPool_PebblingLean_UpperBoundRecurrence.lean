-- Prove2me | Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
-- name    : LeanPool_PebblingLean_UpperBoundRecurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:54:08.420253+00:00
-- url     : https://prove2.me/theorems/11dd9dde-b281-4c34-b491-a9225cb5d5b9
-- title:
--   Upper Bound Recurrence
-- statement:
--   Definitions and structural lemmas for Upper Bound Recurrence, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundRecurrence.lean

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
def HasHypercubePebblingUpperBound (costBound : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, Pebbling.HasSolvableAtMostSize (graph n) 1 (costBound n)
end Hypercube
end PebblingLean


