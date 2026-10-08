-- Prove2me | Definitions.Def_EuclideanRamseyNine
-- name    : EuclideanRamseyNine
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.420616+00:00
-- url     : https://prove2.me/theorems/96dd7e3e-1c40-48f5-ac0b-34796c95ba66
-- statement:
--   For each nonnegative integer d, Space(d) is d-dimensional real Euclidean space. Two indexed configurations a₀, …, aₛ₋₁ in Space(d) and b₀, …, bₛ₋₁ in Space(D) are Congruent when every corresponding pair has the same distance: dist(bᵢ,bⱼ)=dist(aᵢ,aⱼ) for all i and j. The defined proposition Ramsey(a) means that, for every integer r≥2, there is an integer D≥1 such that every coloring of Space(D) with r colors contains a congruent monochromatic configuration b: all its indexed points receive one common color. No regularity is required of the coloring, and the configurations need not have distinct points. For nine arbitrary real parameters t₀, …, t₈, literalCircleConfig assigns point i the two-dimensional vector ((1−tᵢ²)/(1+tᵢ²), 2tᵢ/(1+tᵢ²)), giving nine indexed points on the unit circle, with repetitions permitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamseyNine.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamseyNine.lean; bytes 16..669
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

namespace NineStatement

def literalCircleConfig (t : Fin 9 → ℝ) (i : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![(1 - (t i)^2) / (1 + (t i)^2),
    (2 * t i) / (1 + (t i)^2)]



end NineStatement
end EuclideanRamsey
end
end OAI


