-- Prove2me | Definitions.Def_BalanceSpecificaton_SynchronizedCoded
-- name    : BalanceSpecificaton_SynchronizedCoded
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:36:03.461226+00:00
-- url     : https://prove2.me/theorems/06fd7e7b-f5dd-4250-a570-77a04b3d511a
-- title:
--   Synchronized Coded
-- statement:
--   Definitions and structural lemmas for Synchronized Coded, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SynchronizedCoded.lean

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {X : ShiftSpace A}
def synchronizingCode (X : ShiftSpace A) (v : Word A) : Set (Word A) :=
  {w | w ≠ [] ∧ ∃ t : Word A, w = v ++ t ∧ w ++ v ∈ language X}
end BalanceSpecification


