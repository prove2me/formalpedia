-- Prove2me | Definitions.Def_Moise_Ch0_Ch1_Extra
-- name    : Moise_Ch0_Ch1_Extra
-- status  : Definition
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T13:39:49.794853+00:00
-- url     : https://prove2.me/theorems/800c94d8-486b-444a-95e9-44c0a43dac3b
-- title:
--   Combinatorial equivalence, cells, manifolds, triangulated manifolds, and complex connectivity
-- statement:
--   Defines combinatorial equivalence `Moise.IsCombinatoriallyEquivalent`, $n$-cells `Moise.IsCell`, combinatorial $n$-cells `Moise.IsCombinatorialCell`, topological $n$-manifolds with boundary `Moise.IsTopologicalManifoldWithBoundary`, manifold boundary `Moise.manifoldBoundary` and interior `Moise.manifoldInterior`, triangulated $n$-manifolds `Moise.IsTriangulatedManifold`, combinatorial boundary `Moise.combinatorialBoundary` (Moise Ch. 0), and connectivity of Euclidean complexes `Moise.EuclideanComplex.IsConnected` (Moise Ch. 1).
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapters 0 and 1.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real
import Definitions.Def_Moise_EuclideanComplex

namespace Moise

/-- Two Euclidean complexes `K₁` and `K₂` are combinatorially equivalent (Moise, Ch. 0) if they
have subdivisions `K₁'` and `K₂'` related by a homeomorphism `f : |K₁'| ≃ₜ |K₂'|` such that both
`f` and `f.symm` are simplicial maps. -/
def IsCombinatoriallyEquivalent {n m : ℕ}
    (K₁ : EuclideanComplex n) (K₂ : EuclideanComplex m) : Prop :=
  ∃ (K₁' : EuclideanComplex n) (K₂' : EuclideanComplex m)
    (_ : K₁'.IsSubdivision K₁) (_ : K₂'.IsSubdivision K₂)
    (f : K₁'.polyhedron ≃ₜ K₂'.polyhedron),
    IsSimplicialMap K₁' K₂' f ∧ IsSimplicialMap K₂' K₁' f.symm

/-- A topological space `X` is an `n`-cell (Moise, Ch. 0) if it is homeomorphic to the closed
unit ball in `ℝⁿ`. -/
def IsCell (n : ℕ) (X : Type*) [TopologicalSpace X] : Prop :=
  Nonempty (X ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- A Euclidean complex `K` in `ℝᵐ` is a combinatorial `n`-cell (Moise, Ch. 0) if it is
PL-homeomorphic to a complex consisting of an `n`-simplex and all of its faces. -/
def IsCombinatorialCell (n : ℕ) {m : ℕ} (K : EuclideanComplex m) : Prop :=
  ∃ (K₀ : EuclideanComplex (n + 1)) (σ : Simplex (n + 1)),
    σ.dim = n ∧
    K₀.simplices = {τ : Simplex (n + 1) | τ.IsFace σ} ∧
    ∃ f : K.polyhedron ≃ₜ K₀.polyhedron, IsPLHomeomorph K K₀ f

/-- A topological space `M` is an `n`-manifold with boundary (Moise, Ch. 0) if it is Hausdorff,
second-countable, and every point has an open neighborhood homeomorphic to an open subset of
the closed upper half-space `{y ∈ ℝⁿ | 0 ≤ y₀}` (for `n > 0`, or `ℝ⁰` for `n = 0`). -/
def IsTopologicalManifoldWithBoundary (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  T2Space M ∧ SecondCountableTopology M ∧
  ∀ x : M, ∃ (U : Set M) (V : Set (EuclideanSpace ℝ (Fin n))),
    IsOpen U ∧ x ∈ U ∧ IsOpen V ∧
    Nonempty (U ≃ₜ {y ∈ V | ∀ h : 0 < n, 0 ≤ y ⟨0, h⟩})

/-- The boundary of a topological `n`-manifold `M` (Moise, Ch. 0): points admitting a half-space
chart sending them to the boundary hyperplane `{y₀ = 0}` (empty when `n = 0`). -/
def manifoldBoundary (n : ℕ) (M : Type*) [TopologicalSpace M] : Set M :=
  {x : M | ∃ (U : Set M) (V : Set (EuclideanSpace ℝ (Fin n)))
    (_ : IsOpen U) (hxU : x ∈ U) (_ : IsOpen V)
    (φ : U ≃ₜ {y ∈ V | ∀ h : 0 < n, 0 ≤ y ⟨0, h⟩}) (h : 0 < n),
    (φ ⟨x, hxU⟩).1 ⟨0, h⟩ = 0}

/-- The interior of a topological `n`-manifold `M` (Moise, Ch. 0): the complement of its
boundary. -/
def manifoldInterior (n : ℕ) (M : Type*) [TopologicalSpace M] : Set M :=
  (manifoldBoundary n M)ᶜ

/-- A Euclidean complex `K` in `ℝᵐ` is a triangulated `n`-manifold (Moise, Ch. 0) if its
polyhedron `|K|` is a topological `n`-manifold with boundary. -/
def IsTriangulatedManifold (n : ℕ) {m : ℕ} (K : EuclideanComplex m) : Prop :=
  IsTopologicalManifoldWithBoundary n K.polyhedron

/-- The combinatorial boundary of a triangulated `n`-manifold `K` (Moise, Ch. 0): for `n ≥ 1`,
the simplices of `K` that are faces of some `(n - 1)`-simplex lying in at most one `n`-simplex
of `K` (empty when `n = 0`). -/
def combinatorialBoundary (n : ℕ) {m : ℕ} (K : EuclideanComplex m) : Set (Simplex m) :=
  if 0 < n then
    {σ ∈ K.simplices | ∃ τ ∈ K.simplices, τ.dim = n - 1 ∧ σ.IsFace τ ∧
      Set.Subsingleton {ρ ∈ K.simplices | ρ.dim = n ∧ τ.IsFace ρ}}
  else ∅

/-- A Euclidean complex `K` is connected (Moise, Ch. 1) if it is nonempty and cannot be written
as the union of two nonempty, disjoint Euclidean subcomplexes. -/
def EuclideanComplex.IsConnected {n : ℕ} (K : EuclideanComplex n) : Prop :=
  K.simplices.Nonempty ∧
  ∀ K₁ K₂ : EuclideanComplex n,
    K₁.simplices.Nonempty → K₂.simplices.Nonempty →
    K₁.simplices ∪ K₂.simplices = K.simplices →
    (K₁.simplices ∩ K₂.simplices).Nonempty

end Moise


