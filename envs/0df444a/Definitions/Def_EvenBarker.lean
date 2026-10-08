-- Prove2me | Definitions.Def_EvenBarker
-- name    : EvenBarker
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.740438+00:00
-- url     : https://prove2.me/theorems/96cd41f2-c658-4e6c-85c7-b8705cd569eb
-- statement:
--   For any type equipped with a distinguished element 1 and a negation operation, IsSign(x) means that x equals 1 or −1. For an integer sequence h₀, …, hₙ₋₁ of length n and a nonnegative integer shift k, its aperiodic autocorrelation is the sum of hⱼhⱼ₊ₖ over 0 ≤ j < n−k, where subtraction of natural numbers is truncated at zero. Thus the sum is empty, and equals zero, when k ≥ n. The predicate IsBarker(h) means that every entry of h is a sign, hence is either 1 or −1, and every nonzero shift k with k < n has aperiodic autocorrelation of absolute value at most 1. No parity or positivity condition is imposed on the length n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EvenBarker.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EvenBarker.lean; bytes 16..471
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace CirculantHadamard

universe u

def IsSign {R : Type u} [One R] [Neg R] (x : R) : Prop :=
  x = 1 ∨ x = -1

namespace Barker
open scoped BigOperators

def aperiodic {n : ℕ} (h : Fin n → ℤ) (k : ℕ) : ℤ :=
  ∑ j : Fin (n - k), h ⟨j.val, by omega⟩ * h ⟨j.val + k, by omega⟩

def IsBarker {n : ℕ} (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧ ∀ k : ℕ, 0 < k → k < n → |aperiodic h k| ≤ 1



end Barker
end CirculantHadamard
end OAI


