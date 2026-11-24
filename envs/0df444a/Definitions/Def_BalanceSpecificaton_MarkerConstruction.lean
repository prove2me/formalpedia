-- Prove2me | Definitions.Def_BalanceSpecificaton_MarkerConstruction
-- name    : BalanceSpecificaton_MarkerConstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:00:58.695958+00:00
-- url     : https://prove2.me/theorems/dcb0cc3b-84c8-4013-af65-e554efca0b42
-- title:
--   Marker Construction
-- statement:
--   Definitions and structural lemmas for Marker Construction, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerConstruction.lean

module
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
public import Definitions.Def_BalanceSpecificaton_MarkedRenewal
public import Definitions.Def_BalanceSpecificaton_MarkerRight
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
public import Definitions.Def_BalanceSpecificaton_Specification
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open MarkerExtension
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)] {Y : ShiftSpace A}
end BalanceSpecification


