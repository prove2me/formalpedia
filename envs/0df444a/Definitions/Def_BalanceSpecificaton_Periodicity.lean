-- Prove2me | Definitions.Def_BalanceSpecificaton_Periodicity
-- name    : BalanceSpecificaton_Periodicity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:59.391353+00:00
-- url     : https://prove2.me/theorems/68275aa1-4c3c-47ed-8545-93f6baf23fc6
-- title:
--   Periodicity
-- statement:
--   Definitions and structural lemmas for Periodicity, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
omit [Fintype A] in
/-- The left shift restricted to a shift space. -/
def shiftMap (X : ShiftSpace A) : X.carrier → X.carrier :=
  fun x => ⟨SymbolicDynamics.FullShift.shift 1 x.val, X.mapsTo 1 x.property⟩
end BalanceSpecification


