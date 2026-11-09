-- Prove2me | Definitions.Def_SPFacilityGraph_IsEdgeTriangulation
-- name    : SPFacilityGraph_IsEdgeTriangulation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:01:27.772489+00:00
-- url     : https://prove2.me/theorems/19aba47d-a961-4ce4-af06-ca9a911174d5
-- title:
--   Finite triangulation of $G^n$ with maximal simplices in edge products
-- statement:
--   A geometric simplicial complex $K$ in $(\mathbb R^k)^n$ satisfies the **region requirement** of a PL attribution on $G^n$ if
--
--   1. $K$ is finite;
--   2. its underlying polyhedron (the union of its closed simplices) is exactly $G^n$;
--   3. every maximal simplex $T$ of $K$ is contained in a product $e_1 \times \dots \times e_n$ of graph edges.
--
--   The maximal simplices form the region family $\mathcal T$ of Definition 3.5.
--
--   **Formalization Note** A triangulation is a Mathlib `Geometry.SimplicialComplex`: a set of nonempty affinely independent finite vertex sets, closed under nonempty subsets, any two of which meet in the convex hull of their common vertices. Its maximal simplices are its `facets`.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Definition 3.5 ("Regions"), p.8; triangulations and maximal simplices, Section 3.1, p.6

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_embed

set_option autoImplicit false

namespace SPFacilityGraph

/-- The region requirement of a PL attribution (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Definition 3.5, "Regions", p.8; Section 3.1,
p.6): `K` is a finite triangulation of `Gⁿ ⊆ (ℝ^k)ⁿ` each of whose maximal simplices is
contained in a product `e₁ × ⋯ × eₙ` of graph edges.

**Formalization Note** A triangulation is a Mathlib `Geometry.SimplicialComplex` (nonempty
affinely independent faces, closed under nonempty subfaces, two faces meeting in the hull of their
common vertices). Finite: `K.faces.Finite`. Its underlying polyhedron `K.space` is exactly the
image of `Gⁿ`. The maximal simplices are `K.facets`; each closed simplex `convexHull s` lies in
`∏ⱼ segment eⱼ` for edges `eⱼ` of `G`. -/
def IsEdgeTriangulation {k : ℕ} (G : MetricGraph k) (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k))) : Prop :=
  K.faces.Finite ∧ K.space = Set.range (G.embed (n := n)) ∧
    ∀ s ∈ K.facets, ∃ e : Fin n → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k),
      (∀ j, e j ∈ G.edges) ∧
        ∀ p ∈ convexHull ℝ (s : Set (Fin n → EuclideanSpace ℝ (Fin k))),
          ∀ j, p j ∈ segment ℝ (e j).1 (e j).2

end SPFacilityGraph


