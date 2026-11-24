-- Prove2me | Definitions.Def_BalanceSpecificaton_IntrinsicErgodicity
-- name    : BalanceSpecificaton_IntrinsicErgodicity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:09:56.797373+00:00
-- url     : https://prove2.me/theorems/ca17424f-7d3a-417b-adde-06ac9a34f5c2
-- title:
--   Intrinsic Ergodicity
-- statement:
--   Definitions and structural lemmas for Intrinsic Ergodicity, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/IntrinsicErgodicity.lean

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Mathlib.Dynamics.Ergodic.Extreme
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
end BalanceSpecification


