-- Prove2me | Definitions.Def_ErdosReciprocal
-- name    : ErdosReciprocal
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.130355+00:00
-- url     : https://prove2.me/theorems/bad20ccb-deaf-46ed-8bc0-76c9bbc4d71d
-- statement:
--   For a set A of natural numbers and a natural number k, HasAP(A,k) means that there are natural numbers a and d with d>0 such that a+i d belongs to A for every integer i with 0≤i<k; thus A contains an arithmetic progression of length k with positive common difference. The real-valued sequence reciprocalTerm(A,n) equals 1/n when n belongs to A and equals zero otherwise, with the reciprocal at n=0 also defined to be zero. ReciprocalProgressionTheorem is the defined proposition that, for every set A of natural numbers, if this sequence is not summable, then HasAP(A,k) holds for every natural number k. This block defines the proposition without establishing it.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ErdosReciprocal.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ErdosReciprocal.lean; bytes 16..513
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Erdos3

def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

end Erdos3

open scoped BigOperators

namespace Erdos3

noncomputable def reciprocalTerm (A : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ A then (n : ℝ)⁻¹ else 0

end Erdos3

namespace Erdos3

def ReciprocalProgressionTheorem : Prop :=
  ∀ A : Set ℕ, ¬ Summable (reciprocalTerm A) → ∀ k : ℕ, HasAP A k

end Erdos3

namespace Erdos3



end Erdos3
end OAI


