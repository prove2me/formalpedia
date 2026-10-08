-- Prove2me | Definitions.Def_SmoothYau
-- name    : SmoothYau
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:39.683996+00:00
-- url     : https://prove2.me/theorems/8b35081f-0763-41db-8fde-d169f7fc71ab
-- statement:
--   Working with real finite-dimensional smooth manifolds M modeled on E, SmoothMetric(E,M) is the type of C∞ positive-definite Riemannian metrics, and the file fixes the four-manifold S²×S¹×S¹ (with its product charted-space and smooth-manifold structures, modeled on Euclidean 2 × Euclidean 1 × Euclidean 1). In the chart at a point p, coordinateVector pushes the ith basis vector forward through the inverse chart, and metricCoefficients is the matrix of g-inner products of these coordinate vectors, used only on the chart target. laplaceBeltrami(g,u,x) is the local-coordinate expression det(g)^(-1/2) ∂_i(det(g)^(1/2) g^{ij} ∂_j u), computed in the chart centered at x. A CoordinateTest records a center point, a compact subset of that chart's target, a derivative order, and a row and column index; IsSmoothNeighborhood(g₀,N) says N contains every metric whose chosen finitely many such tests, namely that the norm of the order-n iterated derivative, at every point of the compact set, of the difference of the chosen coefficient entries between g and g₀ is below a single positive ε. nodalMeasure(g,d,u) is the d-dimensional Hausdorff measure, for the path distance of g itself, of the zero set of u. HasUnboundedNodalRatio(g,d) asserts there are smooth nonzero eigenfunctions u_j with positive eigenvalues λ_j satisfying −Δ_g u_j = λ_j u_j, each with finite (d−1)-dimensional nodal measure, such that λ_j tends to infinity and nodal measure divided by √λ_j also tends to infinity. Finally IsRound(g) on S³ states that g equals the pullback of the Euclidean inner product under the inclusion S³ into Euclidean 4-space.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SmoothYau.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SmoothYau.lean; bytes 16..5959
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal


abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Euclidean (n + 1)) 1
abbrev FourManifold := Sphere 2 × (Circle × Circle)
abbrev FourModel := Euclidean 2 × (Euclidean 1 × Euclidean 1)

instance torusChartedSpace : ChartedSpace (Euclidean 1 × Euclidean 1) (Circle × Circle) :=
  prodChartedSpace (Euclidean 1) Circle (Euclidean 1) Circle

instance torusIsManifold : IsManifold 𝓘(ℝ, Euclidean 1 × Euclidean 1) ∞ (Circle × Circle) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod Circle Circle

instance fourChartedSpace : ChartedSpace FourModel FourManifold :=
  prodChartedSpace (Euclidean 2) (Sphere 2) (Euclidean 1 × Euclidean 1) (Circle × Circle)

instance fourIsManifold : IsManifold 𝓘(ℝ, FourModel) ∞ FourManifold := by
  rw [show 𝓘(ℝ, FourModel) = 𝓘(ℝ, Euclidean 2).prod
    𝓘(ℝ, Euclidean 1 × Euclidean 1) from modelWithCornersSelf_prod]
  exact IsManifold.prod (Sphere 2) (Circle × Circle)

section Definitions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Ordinary smooth positive-definite Riemannian metrics, with the existing tangent topology. -/
abbrev SmoothMetric (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] :=
  ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)

abbrev CoordIndex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] := Fin (Module.finrank ℝ E)

/-- A coordinate vector, pushed from a chart back into the tangent bundle. -/
def coordinateVector (p : M) (y : E) (i : CoordIndex E) :
    TangentSpace 𝓘(ℝ, E) ((chartAt E p).symm y) :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y (Module.finBasis ℝ E i)

/-- Metric coefficients in a chart. Only values in the chart target are used. -/
def metricCoefficients (g : SmoothMetric E M) (p : M) (y : E) :
    Matrix (CoordIndex E) (CoordIndex E) ℝ :=
  fun i j => g.inner ((chartAt E p).symm y)
    (coordinateVector p y i) (coordinateVector p y j)

/-- The local coordinate formula det(g)^(-1/2) d_i(det(g)^(1/2) g^{ij} d_j u).
The chart at the evaluation point is used, so all derivatives are taken in
its open target. -/
def laplaceBeltrami (g : SmoothMetric E M) (u : M → ℝ) (x : M) : ℝ :=
  let c := chartAt E x
  let a := metricCoefficients g x
  let density := fun y => Real.sqrt (Matrix.det (a y))
  let u' := u ∘ c.symm
  (density (c x))⁻¹ * ∑ i, fderiv ℝ
    (fun y => density y * ∑ j, (a y)⁻¹ i j *
      fderiv ℝ u' y (Module.finBasis ℝ E j))
    (c x) (Module.finBasis ℝ E i)

/-- One compact-chart seminorm test for the usual smooth topology of metrics. -/
structure CoordinateTest (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M] where
  center : M
  compactSet : Set E
  isCompact : IsCompact compactSet
  inTarget : compactSet ⊆ (chartAt E center).target
  order : ℕ
  row : CoordIndex E
  column : CoordIndex E

/-- The finite compact-chart derivative tests defining a C∞ neighborhood.
A single positive tolerance suffices for the finitely many tests. -/
def IsSmoothNeighborhood (g₀ : SmoothMetric E M) (N : Set (SmoothMetric E M)) : Prop :=
  ∃ tests : List (CoordinateTest E M), ∃ ε : ℝ, 0 < ε ∧
    ∀ g : SmoothMetric E M,
      (∀ t ∈ tests, ∀ y ∈ t.compactSet,
        ‖iteratedFDeriv ℝ t.order
          (fun z => metricCoefficients g t.center z t.row t.column -
            metricCoefficients g₀ t.center z t.row t.column) y‖ < ε) → g ∈ N

/-- Hausdorff measure for the path distance of the actual Riemannian metric,
not the metric inherited from any ambient embedding. -/
def nodalMeasure [T3Space M] (g : SmoothMetric E M) (d : ℝ) (u : M → ℝ) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  Measure.hausdorffMeasure d {x | u x = 0}

/-- The eigensequence belongs to one fixed metric and has finite nodal measure. -/
def HasUnboundedNodalRatio [T3Space M] (g : SmoothMetric E M) (d : ℕ) : Prop :=
  ∃ (u : ℕ → M → ℝ) (eigenvalue : ℕ → ℝ),
    (∀ j, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (u j) ∧ u j ≠ 0 ∧ 0 < eigenvalue j ∧
      (∀ x, -laplaceBeltrami g (u j) x = eigenvalue j * u j x) ∧
      nodalMeasure g (d - 1 : ℕ) (u j) ≠ (∞ : ℝ≥0∞)) ∧
    Tendsto eigenvalue atTop atTop ∧
    Tendsto (fun j => (nodalMeasure g (d - 1 : ℕ) (u j)).toReal / Real.sqrt (eigenvalue j))
      atTop atTop

end Definitions

/-- The round metric is the pullback of the Euclidean scalar product under
inclusion of the unit sphere. This predicate specifies exactly that tensor. -/
def IsRound (g : SmoothMetric (Euclidean 3) (Sphere 3)) : Prop :=
  ∀ (x : Sphere 3) (v w : TangentSpace 𝓘(ℝ, Euclidean 3) x),
    g.inner x v w = inner ℝ
      (mfderiv 𝓘(ℝ, Euclidean 3) 𝓘(ℝ, Euclidean 4)
        (fun y : Sphere 3 => (y : Euclidean 4)) x v)
      (mfderiv 𝓘(ℝ, Euclidean 3) 𝓘(ℝ, Euclidean 4)
        (fun y : Sphere 3 => (y : Euclidean 4)) x w)


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal




end YauCounterexamples
end
end OAI


