-- Prove2me | Definitions.Def_Erdos684_Finite
-- name    : Erdos684_Finite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:10:21.092084+00:00
-- url     : https://prove2.me/theorems/51e679ec-9207-4dc8-97e6-3445a1e65567
-- title:
--   Finite
-- statement:
--   Definitions and structural lemmas for Finite, from AItoBit (AItoBit/erdos-684-elementary-bounds; see pinned Apache-2.0 LICENSE and README.md)'s pinned Elementary upper and lower bounds for Erdos Problem 684 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos684
def smallPrimePart (n k : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE k, p ^ ((n.choose k).factorization p)
end Erdos684


