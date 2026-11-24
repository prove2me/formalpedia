-- Prove2me | Definitions.Def_BalanceSpecificaton_Specification
-- name    : BalanceSpecificaton_Specification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:14.87875+00:00
-- url     : https://prove2.me/theorems/3a24adfc-f2f6-4bfb-b4a0-b9e8f535acda
-- title:
--   Specification
-- statement:
--   Definitions and structural lemmas for Specification, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Specification.lean

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
def shortWords (N : ℕ) : Finset (Word A) := by
  classical
  exact (Finset.range (N + 1)).biUnion (fun n => allWords n)
end BalanceSpecification


