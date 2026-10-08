-- Prove2me | Definitions.Def_SurfaceImmersion
-- name    : SurfaceImmersion
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:26.881667+00:00
-- url     : https://prove2.me/theorems/1176bc6d-8a27-48f4-a42a-63f755a9b87a
-- statement:
--   Over a compact, Hausdorff, second-countable topological space M carrying a smooth charted structure modeled on the Euclidean plane ℝ² (a closed smooth surface), SmoothMetric M is the type of smooth (C^∞) Riemannian metrics on the tangent bundle, with each tangent space modeled on the plane. The ambient space is four-dimensional Euclidean space ℝ⁴, and both manifold models are the standard ones with corners (the whole vector space). For a smooth Riemannian metric g on M and a map F from M to ℝ⁴, IsSmoothIsometricImmersion(g,F) is the proposition that F is C^∞ as a map of manifolds and, for every point p and all tangent vectors v and w at p, the Euclidean inner product of the derivatives dF_p(v) and dF_p(w) equals g_p(v,w), so F pulls back the standard inner product of ℝ⁴ to g. The definition does not separately require injectivity of F or of its derivative. The file also opens a section for finite-order smoothing with the same manifold assumptions, but it contains no further definitions or results.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SurfaceImmersion.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SurfaceImmersion.lean; bytes 16..1055
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open Bundle Manifold
open scoped ContDiff

namespace ClosedSurfaceR4

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev planeModel := 𝓘(ℝ, Plane)
abbrev spaceModel := 𝓘(ℝ, Space)

section

variable (M : Type*) [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

abbrev SmoothMetric :=
  Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
    (fun p : M => TangentSpace planeModel p)

def IsSmoothIsometricImmersion (g : SmoothMetric M) (F : M → Space) : Prop :=
  ContMDiff planeModel spaceModel ∞ F ∧
  ∀ (p : M) (v w : TangentSpace planeModel p),
    inner ℝ (mfderiv planeModel spaceModel F p v)
      (mfderiv planeModel spaceModel F p w) = g.inner p v w

end

namespace FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]



end FiniteOrderSmoothing
end ClosedSurfaceR4
end
end OAI


