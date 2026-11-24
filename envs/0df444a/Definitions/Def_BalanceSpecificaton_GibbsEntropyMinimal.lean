-- Prove2me | Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
-- name    : BalanceSpecificaton_GibbsEntropyMinimal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:38:37.814869+00:00
-- url     : https://prove2.me/theorems/59644296-0b56-49eb-b1fe-d7d57408f234
-- title:
--   Gibbs Entropy Minimal
-- statement:
--   Definitions and structural lemmas for Gibbs Entropy Minimal, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsEntropyMinimal.lean

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A]
def subshiftCylinderEvent (X Y : ShiftSpace A) (n : ℕ) : Set X.carrier :=
  ⋃ w ∈ wordFinset (language Y) (2 * n + 1), cylinder X w (-(n : ℤ))
variable [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
end BalanceSpecification


