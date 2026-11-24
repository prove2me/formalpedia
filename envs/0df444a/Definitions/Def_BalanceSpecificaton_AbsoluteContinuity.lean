-- Prove2me | Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
-- name    : BalanceSpecificaton_AbsoluteContinuity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:09:33.375075+00:00
-- url     : https://prove2.me/theorems/e98fe3ea-6b21-4632-a002-2ba2a5db066b
-- title:
--   Absolute Continuity
-- statement:
--   Definitions and structural lemmas for Absolute Continuity, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/AbsoluteContinuity.lean

module
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
end BalanceSpecification.FiniteEntropy
namespace BalanceSpecification
open MeasureTheory Set Filter
open scoped Topology symmDiff
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
end BalanceSpecification


