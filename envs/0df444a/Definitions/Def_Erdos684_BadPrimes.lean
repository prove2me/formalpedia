-- Prove2me | Definitions.Def_Erdos684_BadPrimes
-- name    : Erdos684_BadPrimes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:10:16.393152+00:00
-- url     : https://prove2.me/theorems/73bafd06-fb9a-565c-a687-f8486a802270
-- title:
--   Bad Primes
-- statement:
--   Definitions and structural lemmas for Bad Primes, from AItoBit (AItoBit/erdos-684-elementary-bounds; see pinned Apache-2.0 LICENSE and README.md)'s pinned Elementary upper and lower bounds for Erdos Problem 684 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/BadPrimes.lean

module
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos684
def badPrimes (n X A : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter fun p => p - n % p ≤ A
end Erdos684


