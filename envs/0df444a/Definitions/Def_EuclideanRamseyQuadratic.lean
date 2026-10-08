-- Prove2me | Definitions.Def_EuclideanRamseyQuadratic
-- name    : EuclideanRamseyQuadratic
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.515315+00:00
-- url     : https://prove2.me/theorems/ec21327c-e7f5-4d31-90e7-5256d2bab470
-- statement:
--   For each nonnegative integer d, Space(d) is d-dimensional real Euclidean space. A configuration a consists of s indexed points in Space(d), with no requirement that the points be distinct. Configurations a and b, possibly in different dimensions, are Congruent when every pair of corresponding points has the same distance. The proposition Ramsey(a) says that for every integer r ≥ 2 there is an integer D ≥ 1 such that every coloring of Space(D) with r colors contains a configuration b congruent to a whose indexed points all have one common color. The coordinate field of a is the smallest subfield of the real numbers containing the rational numbers and all coordinates of all points of a. Coeff(a) is this field, and coordinate(a,i,j) is the jth coordinate of point i regarded as an element of it. The augmented coordinate vector of point i has one additional coordinate equal to 1, followed by its d coordinates in Coeff(a).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamseyQuadratic.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamseyQuadratic.lean; bytes 16..1050
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

def coordinateField {s d : ℕ} (a : Fin s → Space d) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ (Set.range (fun ij : Fin s × Fin d => a ij.1 ij.2))

abbrev Coeff {s d : ℕ} (a : Fin s → Space d) := ↥(coordinateField a)

def coordinate {s d : ℕ} (a : Fin s → Space d) (i : Fin s) (j : Fin d) : Coeff a :=
  ⟨a i j, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self (i, j))⟩

def augmented {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : Option (Fin d) → Coeff a
  | none => 1
  | some j => coordinate a i j



end EuclideanRamsey
end
end OAI


