-- Prove2me | Definitions.Def_Erdos684_Averaging
-- name    : Erdos684_Averaging
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:19:38.473705+00:00
-- url     : https://prove2.me/theorems/f47ca48d-27cf-4d05-91be-64747c1c642e
-- title:
--   Averaging
-- statement:
--   Definitions and structural lemmas for Averaging, from AItoBit (AItoBit/erdos-684-elementary-bounds; see pinned Apache-2.0 LICENSE and README.md)'s pinned Elementary upper and lower bounds for Erdos Problem 684 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Averaging.lean

module
public import Definitions.Def_Erdos684_Finite
public import Definitions.Def_Erdos684_BadPrimes
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Finset Real
namespace Erdos684
def goodPrimes (n X A : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter fun p => A < p - n % p
noncomputable def primeWeight (n k p : ℕ) : ℝ :=
  if p ≤ k then ((n.choose k).factorization p : ℝ) * log p else 0
end Erdos684


