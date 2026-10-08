-- Prove2me | Definitions.Def_BorsukNine
-- name    : BorsukNine
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.336342+00:00
-- url     : https://prove2.me/theorems/e471b649-879d-43e2-9ff2-770df50caee2
-- statement:
--   Vector4 is four-dimensional real Euclidean space, and Matrix4 is the Euclidean space of real 4 × 4 matrices, whose norm is the Frobenius norm. For a vector u, projector(u) is the matrix with entries uᵢuⱼ. The set projectorSet consists of these matrices for unit vectors u, so its elements are the orthogonal projections onto one-dimensional subspaces of ℝ⁴. The set traceOneSymmetric consists of all symmetric real 4 × 4 matrices whose diagonal entries sum to one; positive semidefiniteness is not required in this definition. HasTenSmallCover is the defined proposition that there exist ten subsets C₀, …, C₉ of projectorSet whose union covers projectorSet and each of whose diameters, measured in the Euclidean matrix metric, is strictly less than √2. These covering sets may overlap or be empty, and no measurability or other regularity condition is imposed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BorsukNine.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BorsukNine.lean; bytes 16..619
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace BorsukNine

abbrev Vector4 := EuclideanSpace ℝ (Fin 4)
abbrev Matrix4 := EuclideanSpace ℝ (Fin 4 × Fin 4)

def projector (u : Vector4) : Matrix4 :=
  WithLp.toLp 2 (fun ij => u ij.1 * u ij.2)

def projectorSet : Set Matrix4 :=
  projector '' {u : Vector4 | ‖u‖ = 1}

def traceOneSymmetric : Set Matrix4 :=
  {A | (∀ i j : Fin 4, A (i, j) = A (j, i)) ∧ ∑ i : Fin 4, A (i, i) = 1}

def HasTenSmallCover : Prop :=
  ∃ C : Fin 10 → Set Matrix4,
    (∀ i, C i ⊆ projectorSet) ∧
    projectorSet ⊆ ⋃ i, C i ∧
    ∀ i, Metric.diam (C i) < Real.sqrt 2



end BorsukNine
end OAI


