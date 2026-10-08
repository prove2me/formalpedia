-- Prove2me | Definitions.Def_EuclideanRamseyTransitive
-- name    : EuclideanRamseyTransitive
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.66348+00:00
-- url     : https://prove2.me/theorems/b4bb715d-7c85-40f6-bd98-bd8126f9edb9
-- statement:
--   For each nonnegative integer d, Space(d) is d-dimensional real Euclidean space. Two configurations a and b, indexed by the same finite set of s labels but possibly lying in different dimensions, are Congruent when the distance between bᵢ and bⱼ equals the distance between aᵢ and aⱼ for every pair of labels i and j. Ramsey(a) is the proposition that, for every integer r ≥ 2, there exists a dimension D ≥ 1 such that every coloring of Space(D) with r colors contains a configuration b congruent to a whose points all have one common color. Configurations are not required to have distinct points, and neither s nor the original dimension d is required to be positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamseyTransitive.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamseyTransitive.lean; bytes 16..505
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace EuclideanRamsey

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k

namespace TransitiveConsequence



end TransitiveConsequence
end EuclideanRamsey
end OAI


