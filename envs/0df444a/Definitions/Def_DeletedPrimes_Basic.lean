-- Prove2me | Definitions.Def_DeletedPrimes_Basic
-- name    : DeletedPrimes_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:43:23.599155+00:00
-- url     : https://prove2.me/theorems/01f70db7-045b-4124-a988-4497e10032d8
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from BingoBaggins/deleted-primes contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Deleted-prime sets: composite window rigidity and exponent arithmetic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean

import Mathlib
set_option autoImplicit false
open Real Filter Topology MeasureTheory
namespace DeletedPrimes
noncomputable section
open Classical
def SFree (S : Set ℕ) (n : ℕ) : Prop := ∀ p ∈ S, ¬ p ∣ n
def count (S : Set ℕ) (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter (SFree S)).card
def muS (S : Set ℕ) (d : ℕ) : ℤ :=
  if ∀ p ∈ d.primeFactors, p ∈ S then ArithmeticFunction.moebius d else 0
def density (S : Set ℕ) : ℝ := ∑' d : ℕ, (muS S d : ℝ) / d
def err (S : Set ℕ) (x : ℝ) : ℝ := (count S x : ℝ) - density S * x
def saw (u : ℝ) : ℝ := Int.fract u - 1 / 2
def dim (S : Set ℕ) : ℝ :=
  sInf {σ : ℝ | 0 ≤ σ ∧ Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))}
def IsRegular (S : Set ℕ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |err S x| ≤ C * x ^ θ
def theta (S : Set ℕ) : ℝ := sInf {θ : ℝ | 0 ≤ θ ∧ IsRegular S θ}
def meanSq (S : Set ℕ) (X : ℝ) : ℝ := X⁻¹ * ∫ x in X..2 * X, err S x ^ 2
def IsMSRegular (S : Set ℕ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → meanSq S X ≤ C * X ^ (2 * θ)
def theta2 (S : Set ℕ) : ℝ := sInf {θ : ℝ | 0 ≤ θ ∧ IsMSRegular S θ}
end
end DeletedPrimes


