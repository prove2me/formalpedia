-- Prove2me | Definitions.Def_SquareDifference
-- name    : SquareDifference
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:25.55565+00:00
-- url     : https://prove2.me/theorems/e06dffb3-ded7-48cd-b92b-aa5687997f0d
-- statement:
--   IsSquareDifferenceFree(A) is a defined predicate on a finite set A of integers. It holds when, for every pair of elements a and b of A (the two may be equal or in either order), and every natural number m with m ≥ 1, the difference a − b is not equal to m². In other words, no difference of two elements of A, taken in either order, is a positive perfect square. Since a − a = 0 is not a positive square, equal elements never violate the condition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SquareDifference.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SquareDifference.lean; bytes 16..191
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace SquareDifference

def IsSquareDifferenceFree (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a - b ≠ (m : ℤ) ^ 2



end SquareDifference
end OAI


