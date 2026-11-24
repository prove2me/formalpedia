-- Prove2me | Definitions.Def_BalanceSpecificaton_MarkedRenewal
-- name    : BalanceSpecificaton_MarkedRenewal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:20.836933+00:00
-- url     : https://prove2.me/theorems/6f5bfa6f-ca8c-4376-b2ec-e30ff322aacb
-- title:
--   Marked Renewal
-- statement:
--   Definitions and structural lemmas for Marked Renewal, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkedRenewal.lean

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.MarkerExtension
variable {A : Type*} [Fintype A]
def generatorCount (P : Set (Word A)) (n : ℕ) : ℕ := wordCount (markedCode P) n
def generatedCount (P : Set (Word A)) (n : ℕ) : ℕ :=
  wordCount (generatedWords (markedCode P)) n
end BalanceSpecification.MarkerExtension


