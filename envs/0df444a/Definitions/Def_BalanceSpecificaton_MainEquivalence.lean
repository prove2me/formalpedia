-- Prove2me | Definitions.Def_BalanceSpecificaton_MainEquivalence
-- name    : BalanceSpecificaton_MainEquivalence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:40:56.363911+00:00
-- url     : https://prove2.me/theorems/234ba02d-e201-48bb-b6ba-136c396c9456
-- title:
--   Main Equivalence
-- statement:
--   Definitions and structural lemmas for Main Equivalence, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MainEquivalence.lean

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_Synchronization
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
end BalanceSpecification


