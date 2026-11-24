-- Prove2me | Definitions.Def_BalanceSpecificaton_FiniteEntropy
-- name    : BalanceSpecificaton_FiniteEntropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:29:57.691801+00:00
-- url     : https://prove2.me/theorems/c1a23a90-3f68-438b-a4ea-d51623311b09
-- title:
--   Finite Entropy
-- statement:
--   Definitions and structural lemmas for Finite Entropy, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiniteEntropy.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
def shannon (p : ι → ℝ) : ℝ :=
  ∑ i, -p i * Real.log (p i)
def divergence (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)
end BalanceSpecification.FiniteEntropy


