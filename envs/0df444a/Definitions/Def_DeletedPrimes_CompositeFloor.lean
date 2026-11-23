-- Prove2me | Definitions.Def_DeletedPrimes_CompositeFloor
-- name    : DeletedPrimes_CompositeFloor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:47:01.564233+00:00
-- url     : https://prove2.me/theorems/9147a480-4ca9-450b-b537-65807299b6a3
-- title:
--   Composite Floor
-- statement:
--   Definitions and structural lemmas for Composite Floor, from BingoBaggins/deleted-primes contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Deleted-prime sets: composite window rigidity and exponent arithmetic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
namespace DeletedPrimes
noncomputable section
structure Frame (S : Set ℕ) : Prop where
  bound : ∀ k : ℕ, 1 ≤ k → ∀ κ μ : ℝ, 0 < κ → 0 < μ → κ < 1 / 2 → κ < 1 - dim S →
    (∀ τ ∈ Set.Icc 0 κ, errExp k (dim S) κ τ ≤ -μ) →
    ∃ δ : ℝ, 0 < δ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℝ, ∀ j : Fin k → ℕ, StrictMono j →
        Y₀ ≤ ∏ i, (2 : ℝ) ^ j i →
        (∀ i, |Real.log ((2 : ℝ) ^ j i) / Real.log (∏ i', (2 : ℝ) ^ j i') - 1 / k| ≤ δ) →
        (∀ i, ((2 : ℝ) ^ j i) ^ (dim S - η) ≤ blockCount S (2 ^ j i)) →
        c * ∏ i, (blockCount S (2 ^ j i) : ℝ) ≤ meanSq S ((∏ i, (2 : ℝ) ^ j i) ^ (1 / κ))
def Quantization (S : Set ℕ) : Prop :=
  theta2 S < dim S → ∃ m : ℕ, 1 ≤ m ∧ MertensLaw S (dim S) m
def LandauAtOne (S : Set ℕ) : Prop := theta2 S < 1 → dim S < 1
end
end DeletedPrimes


