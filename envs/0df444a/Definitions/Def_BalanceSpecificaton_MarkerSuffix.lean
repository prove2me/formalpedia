-- Prove2me | Definitions.Def_BalanceSpecificaton_MarkerSuffix
-- name    : BalanceSpecificaton_MarkerSuffix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:19.943942+00:00
-- url     : https://prove2.me/theorems/eb4d21ba-bb72-406e-8791-959bb9f2d58a
-- title:
--   Marker Suffix
-- statement:
--   Definitions and structural lemmas for Marker Suffix, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}
section Payloads
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
variable [Fintype A]
def payloadSuffixFinset (l : ℕ) : Finset (Word A) := by
  classical
  exact (wordFinset (language Y) l).filter
    (fun z => ∃ u : PositiveLanguage Y, z <:+ sourcePayload M hM x s u)
end Payloads
end BalanceSpecification.MarkerExtension


