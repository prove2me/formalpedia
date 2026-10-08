-- Prove2me | Definitions.Def_ProjectionCounterexample
-- name    : ProjectionCounterexample
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:11.744111+00:00
-- url     : https://prove2.me/theorems/b59585e3-fd0a-41c1-9471-c50ade0a9daf
-- statement:
--   For a natural number d, E(d) is d-dimensional real Euclidean space, and simplex(d) is the convex hull in E(d) of the origin together with the d standard basis vectors. IsConvexBody(P) for a subset P of E(d) means that P is compact, convex, and has nonempty interior. For a vector u, project(u) is the continuous linear orthogonal projection onto the orthogonal complement of the line spanned by u. projectionVolume(P,u) is the real number obtained by applying the (d-1)-dimensional Euclidean Hausdorff measure to the image of P under project(u) and converting the extended nonnegative value to a real number with toReal (so an infinite value would become 0); here d-1 is natural-number subtraction. projectionBody(P) is the set of points x such that, for every unit vector u, the inner product of u and x is at most projectionVolume(P,u). bodyVolume(P) is the Lebesgue volume of P converted to a real number by toReal. Finally ratio(P) is bodyVolume(projectionBody(P)) divided by bodyVolume(P) raised to the power d-1. These are only definitions and state no theorem or counterexample claim; IsConvexBody and simplex are defined but not used inside the other definitions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ProjectionCounterexample.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ProjectionCounterexample.lean; bytes 192..1141
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def simplex (d : ℕ) : Set (E d) :=
  convexHull ℝ (insert 0 (range fun i : Fin d => EuclideanSpace.single i (1 : ℝ)))

def IsConvexBody {d : ℕ} (P : Set (E d)) : Prop :=
  IsCompact P ∧ Convex ℝ P ∧ (interior P).Nonempty

def project {d : ℕ} (u : E d) : E d →L[ℝ] E d :=
  (ℝ ∙ u)ᗮ.starProjection

def projectionVolume {d : ℕ} (P : Set (E d)) (u : E d) : ℝ :=
  (Measure.euclideanHausdorffMeasure (d - 1) (project u '' P)).toReal

def projectionBody {d : ℕ} (P : Set (E d)) : Set (E d) :=
  {x | ∀ u : E d, ‖u‖ = 1 → ⟪u, x⟫ ≤ projectionVolume P u}

def bodyVolume {d : ℕ} (P : Set (E d)) : ℝ := (volume P).toReal

def ratio {d : ℕ} (P : Set (E d)) : ℝ :=
  bodyVolume (projectionBody P) / bodyVolume P ^ (d - 1)



end ProjectionCounterexample
end
end OAI


