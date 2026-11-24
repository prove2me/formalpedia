-- Prove2me | Definitions.Def_BalanceSpecificaton_CountBounds
-- name    : BalanceSpecificaton_CountBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:30:50.796982+00:00
-- url     : https://prove2.me/theorems/19581d13-2719-4287-957a-5118ad1b1aa8
-- title:
--   Count Bounds
-- statement:
--   Definitions and structural lemmas for Count Bounds, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
def reverseLanguage (L : Set (Word A)) : Set (Word A) := {w | w.reverse ∈ L}
omit [Fintype A] in
theorem IsFactorial.reverseLanguage (hL : IsFactorial L) :
    IsFactorial (reverseLanguage L) := by
  intro u v huv hv
  exact hL huv.reverse hv
end BalanceSpecification


