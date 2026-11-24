-- Prove2me | Definitions.Def_BalanceSpecificaton_MarkerWordBounds
-- name    : BalanceSpecificaton_MarkerWordBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:59.13427+00:00
-- url     : https://prove2.me/theorems/1ab518a7-8a14-4f03-a9a9-0c24efa7adf2
-- title:
--   Marker Word Bounds
-- statement:
--   Definitions and structural lemmas for Marker Word Bounds, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
def endingMarkerFinset (X : ShiftSpace (Option A)) (n : ℕ) : Finset (Word (Option A)) := by
  classical
  exact (wordFinset (language X) n).filter (fun w => ∃ u, w = u ++ [none])
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
end BalanceSpecification.MarkerExtension


