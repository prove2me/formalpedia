-- Prove2me | Definitions.Def_PettyProjectionVolume
-- name    : PettyProjectionVolume
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:03.15389+00:00
-- url     : https://prove2.me/theorems/c6a78fff-2aaf-45f9-a9c5-f2eacfaeada3
-- statement:
--   Working in n-dimensional real Euclidean space Space(n), IsConvexBody(K) means K is compact, convex, and has nonempty interior. unitBall(n) is the closed Euclidean unit ball centered at the origin, and kappa(n) is its Lebesgue volume. For a vector u, perpendicular(u) is the orthogonal complement of the line spanned by u, a hyperplane when u is nonzero, and shadowVolume(K,u) is the volume, in the Euclidean structure induced on that subspace, of the orthogonal projection of K onto perpendicular(u). projectionBody(K) is the set of points x such that for every unit vector u, the inner product of u and x is at most shadowVolume(K,u); that is, an intersection of half-spaces whose support values are the shadow volumes. projectionRatio(K) is the volume of projectionBody(K) divided by the volume of K raised to the natural-number power n-1, where n-1 is truncated subtraction. pettyConstant(n) is kappa(n-1)^n times kappa(n) raised to the integer power 2-n. Finally, IsEllipsoid(K) means that K is the image of the unit ball under an affine map x -> a + T x, with a a translation vector and T an invertible real-linear map of the space. These are definitions only; no inequality relating projectionRatio and pettyConstant is stated in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PettyProjectionVolume.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PettyProjectionVolume.lean; bytes 16..1425
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace PettyProjection

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def unitBall (n : ℕ) : Set (Space n) := Metric.closedBall 0 1

def kappa (n : ℕ) : ℝ := volume.real (unitBall n)

def perpendicular {n : ℕ} (u : Space n) : Submodule ℝ (Space n) :=
  (Submodule.span ℝ {u})ᗮ

/-- Volume in the induced Euclidean structure on the orthogonal hyperplane. -/
def shadowVolume {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  (volume : Measure (perpendicular u)).real
    ((perpendicular u).orthogonalProjectionOnto '' K)

/-- The body with support function equal to the volumes of orthogonal shadows,
expressed as its defining intersection of supporting half-spaces. -/
def projectionBody {n : ℕ} (K : Set (Space n)) : Set (Space n) :=
  {x | ∀ u : Space n, ‖u‖ = 1 → ⟪u, x⟫ ≤ shadowVolume K u}

def projectionRatio {n : ℕ} (K : Set (Space n)) : ℝ :=
  volume.real (projectionBody K) / volume.real K ^ (n - 1)

def pettyConstant (n : ℕ) : ℝ :=
  kappa (n - 1) ^ n * kappa n ^ (2 - (n : ℤ))

def IsEllipsoid {n : ℕ} (K : Set (Space n)) : Prop :=
  ∃ (a : Space n) (T : Space n ≃ₗ[ℝ] Space n),
    K = (fun x => a + T x) '' unitBall n



end PettyProjection
end
end OAI


