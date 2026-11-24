-- Prove2me | Definitions.Def_BalanceSpecificaton_Results
-- name    : BalanceSpecificaton_Results
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:50:05.68175+00:00
-- url     : https://prove2.me/theorems/c3bc843c-d719-4314-b173-74525eb894f5
-- title:
--   Results
-- statement:
--   Definitions and structural lemmas for Results, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Results.lean

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Definitions.Def_BalanceSpecificaton_Specification
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
end BalanceSpecification


