-- Prove2me | Definitions.Def_ProjectionVolume
-- name    : ProjectionVolume
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:59.848768+00:00
-- url     : https://prove2.me/theorems/8df79ce0-c847-4868-a317-8b613fb4aa9f
-- statement:
--   For a natural number d, simplexConstant(d) is the real number (d+1)·d^d/d!. Euclidean(n) is real Euclidean space ℝⁿ, and for a vector u, normalHyperplane(u) is the orthogonal complement of the line spanned by u (the whole space when u=0). For a set K, projectionVolume(K,u) is the extended-nonnegative-real volume, taken with respect to the volume measure on that hyperplane, of the image of K under orthogonal projection onto it. The brightness of K in direction u is ‖u‖ times the real value of this projection volume (truncating an infinite value to zero), so it scales with the length of u. projectionBody(K) is the set of points y such that ⟨u,y⟩ ≤ brightness(K,u) for every vector u. normalizedProjectionVolume(K) is the real value of the volume of projectionBody(K) divided by the real value of vol(K) raised to the natural-number power n−1, where n−1 is truncated subtraction. standardSimplex(n) is the convex hull of the origin and the n standard basis vectors of ℝⁿ. For x in ℝ²⁰, firstBlock(x) and secondBlock(x) are the vectors in ℝ¹⁰ formed by its first ten and last ten coordinates, and productWitness is the set of x in ℝ²⁰ whose two blocks both lie in standardSimplex(10), a product of two 10-dimensional standard simplices. These are definitions only, with no theorem asserted about them.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ProjectionVolume.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ProjectionVolume.lean; bytes 16..1492
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

noncomputable def simplexConstant (d : ℕ) : ℝ :=
  (d + 1) * (d : ℝ) ^ d / d.factorial

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def normalHyperplane {n : ℕ} (u : Euclidean n) : Submodule ℝ (Euclidean n) :=
  (Submodule.span ℝ ({u} : Set (Euclidean n)))ᗮ

def projectionVolume {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : ENNReal :=
  (volume : Measure (normalHyperplane u))
    ((normalHyperplane u).orthogonalProjectionOnto '' K)

def brightness {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : ℝ :=
  ‖u‖ * (projectionVolume K u).toReal

def projectionBody {n : ℕ} (K : Set (Euclidean n)) : Set (Euclidean n) :=
  {y | ∀ u, ⟪u, y⟫ ≤ brightness K u}

def normalizedProjectionVolume {n : ℕ} (K : Set (Euclidean n)) : ℝ :=
  (volume (projectionBody K)).toReal / (volume K).toReal ^ (n - 1)

def standardSimplex (n : ℕ) : Set (Euclidean n) :=
  convexHull ℝ (insert 0 (Set.range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)))

def firstBlock (x : Euclidean 20) : Euclidean 10 :=
  WithLp.toLp 2 (fun i : Fin 10 => x (Fin.castAdd 10 i))

def secondBlock (x : Euclidean 20) : Euclidean 10 :=
  WithLp.toLp 2 (fun i : Fin 10 => x (Fin.natAdd 10 i))

def productWitness : Set (Euclidean 20) :=
  {x | firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10}



end Paper092
end
end OAI


