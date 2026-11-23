-- Prove2me | Definitions.Def_DeletedPrimes_Legendre
-- name    : DeletedPrimes_Legendre
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:44:21.804017+00:00
-- url     : https://prove2.me/theorems/4e97cfe6-6c5a-4410-8f49-173d6565d1a3
-- title:
--   Legendre
-- statement:
--   Definitions and structural lemmas for Legendre, from BingoBaggins/deleted-primes contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Deleted-prime sets: composite window rigidity and exponent arithmetic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean

import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology
namespace DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
def unitSum (S : Set ℕ) (σ : ℝ) : ℝ := ∑' d : ℕ, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ)
def mertensS (S : Set ℕ) (x : ℝ) : ℝ := ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ)
theorem muS_zero (S : Set ℕ) : muS S 0 = 0 := by
  simp [muS]
def muSFun (S : Set ℕ) : ArithmeticFunction ℤ := ⟨muS S, muS_zero S⟩
def sfreeFun (S : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ SFree S n then 1 else 0, by simp⟩
end
end DeletedPrimes


