-- Prove2me | Definitions.Def_SPFacilityGraph_MetricGraph
-- name    : SPFacilityGraph_MetricGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:46.569006+00:00
-- url     : https://prove2.me/theorems/a2bd899e-1883-4cca-a403-056137aac512
-- title:
--   Straight-edge metric graph $G \subseteq \mathbb R^k$
-- statement:
--   A **metric graph** $G$ is a connected compact subset of Euclidean space $\mathbb R^k$ that is the union of finitely many edges. Each edge has two distinct endpoints (the vertices), distinct edges meet only at endpoints common to both, and there is at least one edge. Under the standing assumption of Section 3.2 every edge is a straight line segment $[a, b] = \{(1-\lambda)a + \lambda b : \lambda \in [0,1]\}$ with $a \ne b$.
--
--   So a metric graph is given by a finite nonempty set of edges $(a, b)$, $a \neq b$, such that for distinct edges $e = (a,b)$, $e' = (a', b')$
--   $$
--   [a, b] \cap [a', b'] \subseteq \{a, b\} \cap \{a', b'\},
--   $$
--   and the union $\bigcup_e [a_e, b_e]$ is connected. All facility-location objects of the mission (profiles, distances, mechanisms, triangulations) live on such a graph.
--
--   **Formalization Note** An edge is an ordered pair of points of `EuclideanSpace ℝ (Fin k)`; the intersection clause forbids listing an edge twice, also in reverse. Compactness, positive finite length and absence of self-intersections are automatic for finitely many straight segments and are not separate fields.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.1, p.4 (definition of a graph), with the standing assumption of Section 3.2, p.6 ("every edge of G is a straight line segment")

import Mathlib

set_option autoImplicit false

namespace SPFacilityGraph

/-- A (straight-edge) metric graph in `ℝ^k` (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.1, p.4, with the standing
assumption of Section 3.2, p.6).

A graph is a connected compact subset of `ℝ^k` that is the union of finitely many edges; each
edge has two distinct endpoints, and distinct edges meet only at common endpoints; every graph has
at least one edge. From Section 3.2 on, every edge is a straight line segment.

**Formalization Note** The Section 3.2 standing assumption (straight edges) is built in: an edge
is an ordered pair `(a, b)` of distinct points of `ℝ^k` (`EuclideanSpace ℝ (Fin k)`), and the
edge itself is `segment ℝ a b`. A straight segment with distinct endpoints has positive finite
length and no self-intersections, and a finite union of segments is compact, so those clauses are
automatic and not bundled. The clause `meet` says that two distinct edges intersect only in
endpoints common to both; it also forbids the reversed copy `(b, a)` of an edge, so each segment
occurs once. `connected` is connectedness of the union of the edges (the carrier). -/
structure MetricGraph (k : ℕ) where
  /-- the edges, each given by its two endpoints -/
  edges : Finset (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
  /-- every graph has at least one edge -/
  edges_nonempty : edges.Nonempty
  /-- each edge has two distinct endpoints -/
  fst_ne_snd : ∀ e ∈ edges, e.1 ≠ e.2
  /-- distinct edges meet only at common endpoints -/
  meet : ∀ e ∈ edges, ∀ e' ∈ edges, e ≠ e' →
    segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
      ({e.1, e.2} : Set (EuclideanSpace ℝ (Fin k))) ∩ {e'.1, e'.2}
  /-- the union of the edges is connected -/
  connected : IsConnected (⋃ e ∈ edges, segment ℝ e.1 e.2)

end SPFacilityGraph


