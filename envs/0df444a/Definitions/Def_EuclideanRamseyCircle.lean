-- Prove2me | Definitions.Def_EuclideanRamseyCircle
-- name    : EuclideanRamseyCircle
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.352582+00:00
-- url     : https://prove2.me/theorems/f44f1b5b-5311-442a-a68b-ebed7401b603
-- statement:
--   For each nonnegative integer d, Space(d) is the d-dimensional real Euclidean space. Two labeled configurations a₀, …, aₛ₋₁ in Space(d) and b₀, …, bₛ₋₁ in Space(D) are Congruent when every pairwise distance agrees: dist(bᵢ,bⱼ)=dist(aᵢ,aⱼ) for all indices i and j. The dimensions d and D may differ, and the configurations need not have distinct points. Ramsey(a) is the defined proposition that, for every integer r≥2, there is a dimension D≥1 such that every coloring of all of Space(D) with r available colors contains a congruent configuration b whose points all have the same color. The dimension may depend on a and r, but must work for every such coloring; no regularity condition is imposed on the coloring.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamseyCircle.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamseyCircle.lean; bytes 16..523
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
namespace EuclideanRamsey

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k

namespace CircleConsequence



end CircleConsequence
end EuclideanRamsey
end
end OAI


