-- Prove2me | Definitions.Def_PrimeGaps
-- name    : PrimeGaps
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:10.300301+00:00
-- url     : https://prove2.me/theorems/24a98c12-9529-45a1-a819-becf0f737c32
-- statement:
--   The block defines prime-indexing and counting notions for prime gaps. In the namespace LargePrimeGaps, prime(n) is the (n-1)-indexed zero-based Nat.nth prime, so prime(1)=2, prime(2)=3, and so on (natural subtraction makes prime(0) equal prime(1)). For a real C and natural N, largeGapIndices(C,N) is the finite set of indices n between 1 and N inclusive such that the gap to the next prime exceeds C times the logarithm of the current prime, namely C·log(p_n) < p_{n+1} − p_n, computed in the reals. In Problem344, primeAt(n) is the same nth-prime function. initialCount(A,N) is the number of elements of a set A of naturals lying in {1,…,N}. lowerAsymptoticDensity(A) is the supremum of all real d for which there is N0 such that d ≤ initialCount(A,N)/N for every N ≥ N0, that is, a lower density of A defined via initial segments starting at 1. ratioIncreaseIndices is the set of n ≥ 1 for which the ratio p_n/n is strictly smaller than p_{n+1}/(n+1), i.e. the sequence of prime-to-index ratios increases from n to n+1. These are definitions only, with no theorem or conjecture asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PrimeGaps.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PrimeGaps.lean; bytes 16..884
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace LargePrimeGaps

noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

noncomputable def largeGapIndices (C : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    C * Real.log (prime n : ℝ) < (prime (n + 1) : ℝ) - (prime n : ℝ)

end LargePrimeGaps

noncomputable section

namespace Problem344

def primeAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

def initialCount (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card

def lowerAsymptoticDensity (A : Set ℕ) : ℝ :=
  sSup {d : ℝ | ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    d ≤ (initialCount A N : ℝ) / (N : ℝ)}

def ratioIncreaseIndices : Set ℕ :=
  {n | 1 ≤ n ∧
    (primeAt n : ℝ) / (n : ℝ) <
      (primeAt (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)}



end Problem344
end
end OAI


