-- Prove2me | Definitions.Def_BalanceSpecificaton_VariationalPrinciple
-- name    : BalanceSpecificaton_VariationalPrinciple
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:11:09.842019+00:00
-- url     : https://prove2.me/theorems/c51a174d-8ee3-4fd7-a205-e6d6ba0c72e0
-- title:
--   Variational Principle
-- statement:
--   Definitions and structural lemmas for Variational Principle, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
def translatedProbability (μ : ProbabilityMeasure X.carrier) (k : ℕ) :
    ProbabilityMeasure X.carrier := μ.map (((show Measurable (shiftMap X) from (measurable_pi_lambda (fun x : X.carrier => SymbolicDynamics.FullShift.shift 1 x.val) fun i : ℤ => (measurable_pi_apply (1 + i)).comp measurable_subtype_coe).subtype_mk).iterate k).aemeasurable)
end BalanceSpecification


