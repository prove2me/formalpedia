-- Prove2me | Definitions.Def_BalanceSpecificaton_GibbsBalance
-- name    : BalanceSpecificaton_GibbsBalance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:09:28.151868+00:00
-- url     : https://prove2.me/theorems/0378912e-94a9-4440-9bf0-6c62479b3c85
-- title:
--   Gibbs Balance
-- statement:
--   Definitions and structural lemmas for Gibbs Balance, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
end BalanceSpecification


