-- Prove2me | Definitions.Def_BalanceSpecificaton_MarkerRight
-- name    : BalanceSpecificaton_MarkerRight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:21.779678+00:00
-- url     : https://prove2.me/theorems/b86152c5-3eeb-4436-afc6-e511cc6a8af4
-- title:
--   Marker Right
-- statement:
--   Definitions and structural lemmas for Marker Right, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerRight.lean

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [TopologicalSpace (Option A)]
  {Y : ShiftSpace A} {X : ShiftSpace (Option A)}
variable [Fintype A]
end BalanceSpecification.MarkerExtension


