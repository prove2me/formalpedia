-- Prove2me | Definitions.Def_BalanceSpecificaton_SGapBSM
-- name    : BalanceSpecificaton_SGapBSM
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:40:35.483143+00:00
-- url     : https://prove2.me/theorems/bcaea5be-6dcb-44b0-b4cd-7e88b0f8d99c
-- title:
--   SGap BSM
-- statement:
--   Definitions and structural lemmas for SGap BSM, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean

module
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open Filter Set
open scoped Topology
end BalanceSpecification


