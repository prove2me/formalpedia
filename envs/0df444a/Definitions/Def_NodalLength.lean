-- Prove2me | Definitions.Def_NodalLength
-- name    : NodalLength
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:20.005926+00:00
-- url     : https://prove2.me/theorems/5ea2d90d-9c21-446e-8704-3334256884da
-- statement:
--   On a metric space M carrying a smooth two-dimensional charted structure (charts into the Euclidean plane) and a Riemannian metric on its tangent bundle, the block defines coordinate expressions of the geometry. For a base point x, coordinateMetric(x,y) is the 2×2 Gram matrix of the pushforwards of the coordinate basis vectors under the inverse of the chart at x, evaluated at plane point y, and coordinateDensity is the square root of its determinant. coordPartial(f,i,y) is the ith partial derivative of f at y. laplaceBeltrami(u,x) is the Laplace–Beltrami operator in the chart at x, namely (1/√det g) ∑_i ∂_i(√det g ∑_j g^{ij} ∂_j(u∘chart⁻¹)), evaluated at the chart image of x. nodalSet(u) is the zero set {u=0}, and nodalLength(u) is its one-dimensional Hausdorff measure with respect to the Borel structure, valued in [0,∞]. MainStatement(M) is a defined proposition, not an established theorem: there is a constant C≥0 such that for every λ>0 and every smooth, not identically zero function u on M satisfying −Δu=λu everywhere, the nodal length of u is at most C√λ. The constant C is quantified before λ and u, so it is uniform over all eigenfunctions, but it is allowed to depend on M.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NodalLength.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/NodalLength.lean; bytes 16..1840
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Plane) x)]

def coordinateMetric (x : M) (y : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => inner ℝ
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (chartAt Plane x).symm y
      (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (chartAt Plane x).symm y
      (EuclideanSpace.single j 1))

def coordinateDensity (x : M) (y : Plane) : ℝ :=
  Real.sqrt (coordinateMetric x y).det

def coordPartial (f : Plane → ℝ) (i : Fin 2) (y : Plane) : ℝ :=
  fderiv ℝ f y (EuclideanSpace.single i 1)

def laplaceBeltrami (u : M → ℝ) (x : M) : ℝ :=
  (coordinateDensity x (chartAt Plane x x))⁻¹ *
    ∑ i : Fin 2, coordPartial (fun y => coordinateDensity x y *
      ∑ j : Fin 2, ((coordinateMetric x y)⁻¹ i j) *
        coordPartial (u ∘ (chartAt Plane x).symm) j y) i (chartAt Plane x x)

def nodalSet (u : M → ℝ) : Set M := {x | u x = 0}

def nodalLength (u : M → ℝ) : ℝ≥0∞ :=
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  Measure.hausdorffMeasure 1 (nodalSet u)

def MainStatement (M : Type*) [MetricSpace M] [ChartedSpace Plane M]
    [IsManifold 𝓘(ℝ, Plane) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Plane) x)] : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℝ), 0 < lam → ∀ (u : M → ℝ),
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ) ∞ u → u ≠ 0 →
    (∀ x, -laplaceBeltrami u x = lam * u x) →
    nodalLength u ≤ ENNReal.ofReal (C * Real.sqrt lam)



end SharpNodal
end
end OAI


