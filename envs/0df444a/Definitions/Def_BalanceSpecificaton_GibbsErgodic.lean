-- Prove2me | Definitions.Def_BalanceSpecificaton_GibbsErgodic
-- name    : BalanceSpecificaton_GibbsErgodic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:35:40.696876+00:00
-- url     : https://prove2.me/theorems/6eea3747-f74e-420b-8b99-943c740be339
-- title:
--   Gibbs Ergodic
-- statement:
--   Definitions and structural lemmas for Gibbs Ergodic, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped symmDiff ENNReal
namespace BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]
end BalanceSpecification


