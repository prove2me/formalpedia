-- Prove2me | Definitions.Def_GaussianPropeller
-- name    : GaussianPropeller
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.900789+00:00
-- url     : https://prove2.me/theorems/46442453-4b53-4236-959f-0fb6cecfceb4
-- statement:
--   For each nonnegative integer d, Space(d) is d-dimensional real Euclidean space and gaussian(d) is its standard Gaussian measure. A family A of k measurable sets is an IsPartition if almost every point under this measure belongs to exactly one member; gaps and overlaps may occur only on Gaussian-null sets. The centroid of a set A is the vector integral of x over A with respect to gaussian(d), an unnormalized first moment, not a conditional mean. The value of a family is the sum of the squared Euclidean norms of its centroids. The function coord(j,x) returns coordinate j, indexing from zero, when j<d, and zero otherwise. Writing x₀=coord(0,x) and x₁=coord(1,x), propeller(d,k) assigns its existing indexed members as follows: member 0 is |x₁|≤√3 x₀; member 1 is x₁≥0 and √3 x₀≤x₁; member 2 is x₁≤0 and √3 x₀≤−x₁; all members indexed 3 or higher are empty. AllPartitions is the proposition that, for every positive dimension d and positive number k of sets, every IsPartition family has value at most 9/(8π), and that for every d≥2 and k≥3, propeller(d,k) is an IsPartition and has value exactly 9/(8π). In that latter range, shared propeller boundaries are Gaussian-null.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianPropeller.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianPropeller.lean; bytes 16..1316
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GaussianPropeller

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def gaussian (d : ℕ) : Measure (Space d) := stdGaussian (Space d)

def IsPartition {d k : ℕ} (A : Fin k → Set (Space d)) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ ∀ᵐ x ∂gaussian d, ∃! i, x ∈ A i

noncomputable def centroid {d : ℕ} (A : Set (Space d)) : Space d :=
  ∫ x in A, x ∂gaussian d

noncomputable def value {d k : ℕ} (A : Fin k → Set (Space d)) : ℝ :=
  ∑ i, ‖centroid (A i)‖ ^ 2

def coord {d : ℕ} (j : ℕ) (x : Space d) : ℝ :=
  if h : j < d then x ⟨j, h⟩ else 0

noncomputable def propeller (d k : ℕ) (i : Fin k) : Set (Space d) :=
  if i.val = 0 then {x | |coord 1 x| ≤ Real.sqrt 3 * coord 0 x}
  else if i.val = 1 then {x | 0 ≤ coord 1 x ∧ Real.sqrt 3 * coord 0 x ≤ coord 1 x}
  else if i.val = 2 then {x | coord 1 x ≤ 0 ∧ Real.sqrt 3 * coord 0 x ≤ -coord 1 x}
  else ∅

def AllPartitions : Prop :=
  (∀ (d k : ℕ), 0 < d → 0 < k → ∀ A : Fin k → Set (Space d),
    IsPartition A → value A ≤ 9 / (8 * Real.pi)) ∧
  (∀ (d k : ℕ), 2 ≤ d → 3 ≤ k →
    IsPartition (propeller d k) ∧ value (propeller d k) = 9 / (8 * Real.pi))



end GaussianPropeller
end OAI


