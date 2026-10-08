-- Prove2me | Definitions.Def_EuclideanRamseySpherical
-- name    : EuclideanRamseySpherical
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.578293+00:00
-- url     : https://prove2.me/theorems/403572aa-6aaf-4b2a-ae03-adda1c032850
-- statement:
--   For each nonnegative integer d, Space(d) is d-dimensional real Euclidean space. Two indexed configurations a₀, …, aₛ₋₁ in Space(d) and b₀, …, bₛ₋₁ in Space(D) are Congruent when all corresponding pairwise distances agree: dist(bᵢ,bⱼ)=dist(aᵢ,aⱼ) for every i and j. The defined proposition Ramsey(a) says that for every integer r≥2 there is an integer D≥1 such that every coloring of Space(D) with r colors contains a monochromatic configuration congruent to a. Explicitly, there must be points b₀, …, bₛ₋₁ preserving those pairwise distances and one color shared by every bᵢ. The dimension D may depend on a and r, but must work for every such coloring. No regularity is required of the coloring, and the indexed configurations need not have distinct points.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamseySpherical.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamseySpherical.lean; bytes 16..520
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k



end EuclideanRamsey
end
end OAI


