-- Prove2me | Definitions.Def_BalanceSpecificaton_EntropyRealization
-- name    : BalanceSpecificaton_EntropyRealization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:30:24.374814+00:00
-- url     : https://prove2.me/theorems/64c690e1-583b-4deb-86fb-ab1958d2e126
-- title:
--   Entropy Realization
-- statement:
--   Definitions and structural lemmas for Entropy Realization, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Filter Set
open scoped Topology
namespace BalanceSpecification
def betaResidual (β a x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => if 1 + a ≤ β * betaResidual β a x n then
      β * betaResidual β a x n - 1 else β * betaResidual β a x n
def betaDigit (β a x : ℝ) (n : ℕ) : ℝ :=
  if 1 + a ≤ β * betaResidual β a x n then 1 else 0
end BalanceSpecification


