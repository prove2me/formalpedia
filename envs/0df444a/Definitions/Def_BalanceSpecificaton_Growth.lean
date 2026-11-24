-- Prove2me | Definitions.Def_BalanceSpecificaton_Growth
-- name    : BalanceSpecificaton_Growth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:29:54.353939+00:00
-- url     : https://prove2.me/theorems/2811b7aa-6509-44be-a459-1e391e3b0133
-- title:
--   Growth
-- statement:
--   Definitions and structural lemmas for Growth, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Growth.lean

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
abbrev Submultiplicative (u : ℕ → ℝ) : Prop := ∀ m n, u (m + n) ≤ u m * u n
namespace BalanceSpecification.Growth
def rate (a : ℕ → ℝ) : ℝ :=
  sInf ((fun n : ℕ => Real.log (a n) / n) '' Ici 1)
def BoundedSupermultiplicative (a : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ m n, a m * a n ≤ c * a (m + n)
end BalanceSpecification.Growth


