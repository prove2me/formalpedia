-- Prove2me | Definitions.Def_BalanceSpecificaton_EntropyContinuity
-- name    : BalanceSpecificaton_EntropyContinuity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:10:19.437485+00:00
-- url     : https://prove2.me/theorems/898d90fa-d8f7-4acb-b9fa-fc3d4e24e55a
-- title:
--   Entropy Continuity
-- statement:
--   Definitions and structural lemmas for Entropy Continuity, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
namespace FiniteEntropy
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
end FiniteEntropy
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
end BalanceSpecification


