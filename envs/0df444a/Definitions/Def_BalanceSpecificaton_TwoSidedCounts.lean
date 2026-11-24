-- Prove2me | Definitions.Def_BalanceSpecificaton_TwoSidedCounts
-- name    : BalanceSpecificaton_TwoSidedCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:32.556349+00:00
-- url     : https://prove2.me/theorems/7171cf1a-2f80-4fd0-81c1-72bdb8a4a357
-- title:
--   Two Sided Counts
-- statement:
--   Definitions and structural lemmas for Two Sided Counts, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TwoSidedCounts.lean

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
def extensionPairs (L : Set (Word A)) (u : Word A) (a b : ℕ) :
    Finset ((_ : Word A) × Word A) := by
  classical
  exact (predecessorFinset L u a).sigma (fun p => followerFinset L (p ++ u) b)
def occurrenceFinset (L : Set (Word A)) (u : Word A) (a b : ℕ) : Finset (Word A) := by
  classical
  exact (extensionPairs L u a b).image (fun ps => ps.1 ++ u ++ ps.2)
end BalanceSpecification


