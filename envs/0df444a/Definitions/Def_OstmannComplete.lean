-- Prove2me | Definitions.Def_OstmannComplete
-- name    : OstmannComplete
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:59.438982+00:00
-- url     : https://prove2.me/theorems/ea1b5495-f238-4196-b5e9-93a3c67f687c
-- statement:
--   The block works with sets of natural numbers, writing primes for the set of prime numbers and sumset(A,B) for the pointwise sumset A+B = {a+b : a∈A, b∈B}. EventuallyPrimeSumset(A,B) says there is a threshold N such that, for every n ≥ N, n lies in A+B exactly when n is prime, so the sumset agrees with the primes from N onward. TwoInfiniteSummandsImpossible is the defined proposition that no two infinite sets A and B satisfy this, that is, the primes cannot be eventually represented as a sumset of two infinite sets. InverseGoldbach is the defined proposition that for any two nontrivial sets A and B (each having at least two distinct elements), the symmetric difference of A+B and the primes, meaning the numbers lying in exactly one of the two sets, is infinite. The symmetric difference is written with an explicitly spelled-out instance path for the Boolean algebra structure on sets. Both are stated only as propositions, not as established theorems.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OstmannComplete.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OstmannComplete.lean; bytes 16..925
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped Pointwise symmDiff

namespace Ostmann

def primes : Set ℕ := {n | Nat.Prime n}

abbrev sumset (A B : Set ℕ) : Set ℕ := A + B

def EventuallyPrimeSumset (A B : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → (n ∈ sumset A B ↔ n.Prime)

def TwoInfiniteSummandsImpossible : Prop :=
  ∀ A B : Set ℕ, A.Infinite → B.Infinite → ¬ EventuallyPrimeSumset A B

def InverseGoldbach : Prop :=
  ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial →
    Set.Infinite (@symmDiff (Set ℕ)
      (@SemilatticeSup.toMax (Set ℕ)
        (@Lattice.toSemilatticeSup (Set ℕ)
          (@CompleteLattice.toLattice (Set ℕ)
            (@CompleteBooleanAlgebra.toCompleteLattice (Set ℕ)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set ℕ)
                (@Set.instCompleteAtomicBooleanAlgebra ℕ))))))
      Set.instSDiff (sumset A B) primes)



end Ostmann
end OAI


