-- Prove2me | Definitions.Def_BalanceSpecificaton_SGapBounds
-- name    : BalanceSpecificaton_SGapBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:29:53.5962+00:00
-- url     : https://prove2.me/theorems/b45e1076-b4a0-43b4-893a-455a126bf293
-- title:
--   SGap Bounds
-- statement:
--   Definitions and structural lemmas for SGap Bounds, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBounds.lean

module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
def HasBoundedSuccessiveGaps (S : Set ℕ) : Prop :=
  ∃ K : ℕ, ∀ a ∈ S, ∀ b ∈ S, a < b →
    (∀ s ∈ S, a < s → b ≤ s) → b - a ≤ K
end BalanceSpecification


