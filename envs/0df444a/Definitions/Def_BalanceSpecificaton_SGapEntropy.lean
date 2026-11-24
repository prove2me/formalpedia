-- Prove2me | Definitions.Def_BalanceSpecificaton_SGapEntropy
-- name    : BalanceSpecificaton_SGapEntropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:39:36.696396+00:00
-- url     : https://prove2.me/theorems/99ea876c-f7b0-42d3-a1d5-f0e6753c2d24
-- title:
--   SGap Entropy
-- statement:
--   Definitions and structural lemmas for SGap Entropy, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open Filter Set
open scoped Topology
end BalanceSpecification


