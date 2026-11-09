-- Prove2me | Definitions.Def_SPFacilityGraph_MetricGraph_dist
-- name    : SPFacilityGraph_MetricGraph_dist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:51:49.935204+00:00
-- url     : https://prove2.me/theorems/b8035c5b-f735-4a97-a4e2-b28eecdd30e7
-- title:
--   Graph distance $d_G(x,y)$
-- statement:
--   The **graph distance** $d_G(x, y)$ between points $x, y \in G$ is the length of a shortest path in $G$ from $x$ to $y$. For a straight-edge graph it is
--   $$
--   d_G(x, y) = \inf\Big\{ \sum_{j=1}^{m} \|p_j - p_{j-1}\| \;:\; p_0 = x,\ p_m = y,\ \text{each } p_{j-1}, p_j \text{ on a common edge} \Big\},
--   $$
--   the infimum of the polygonal lengths of walks in $G$ from $x$ to $y$ that move along edges. It is the intrinsic distance of the graph, not the Euclidean distance of $\mathbb R^k$: on an equilateral triangle with unit edges the midpoints of two edges are at graph distance $1$ but Euclidean distance $1/2$.
--
--   **Formalization Note** The paper defines $d_G(x,y)$ as the minimum length over paths (minimal connected subsets of $G$ containing $x$ and $y$). On a straight-edge graph every such path is traced by a walk of the same length and every walk contains a path of no greater length, so the two agree. Walks are finite lists of points. Connectedness of $G$ makes the set of walks nonempty and lengths are nonnegative, so the infimum is a genuine real number.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.1, p.4 (d_G(x, y) = min_γ len(γ))

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_Pt

set_option autoImplicit false

namespace SPFacilityGraph

/-- The graph distance `d_G(x, y)` (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.1, p.4): the minimum length of a path in
`G` between `x` and `y`.

Here it is the infimum, over all finite walks `x = p₀, p₁, …, p_m = y` in which every two
consecutive points lie on one common edge segment, of the polygonal length
`∑ⱼ ‖pⱼ − pⱼ₋₁‖`.

**Formalization Note** For a straight-edge graph (Section 3.2) a path between `x` and `y` (a
minimal connected subset containing both) is a finite union of pieces of edges, so it is traced
by such a walk with the same length, and every walk contains a path between its ends of no greater
length; hence this infimum is the paper's minimum. The set of walks is nonempty because the
carrier is connected, and all lengths are `≥ 0`, so the real `sInf` takes no junk value. The
Euclidean norm enters only along a single edge segment; `d_G` is not the Euclidean distance. -/
noncomputable def MetricGraph.dist {k : ℕ} (G : MetricGraph k) (x y : G.Pt) : ℝ :=
  sInf {L : ℝ | ∃ l : List (EuclideanSpace ℝ (Fin k)),
    l.head? = some (x : EuclideanSpace ℝ (Fin k)) ∧
    l.getLast? = some (y : EuclideanSpace ℝ (Fin k)) ∧
    l.IsChain (fun a b => ∃ e ∈ G.edges, a ∈ segment ℝ e.1 e.2 ∧ b ∈ segment ℝ e.1 e.2) ∧
    L = ((l.zip l.tail).map fun p => ‖p.2 - p.1‖).sum}

end SPFacilityGraph


