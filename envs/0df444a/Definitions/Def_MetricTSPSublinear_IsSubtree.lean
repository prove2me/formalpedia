-- Prove2me | Definitions.Def_MetricTSPSublinear_IsSubtree
-- name    : MetricTSPSublinear_IsSubtree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:30:59.449922+00:00
-- url     : https://prove2.me/theorems/7e9c2f85-be9a-4efc-9234-c1789e11c47d
-- title:
--   Subtrees of the continuous extension $R(T)$
-- statement:
--   A **subtree** of $R(T)$ is a closed connected subset of $R(T)$; it may contain parts of edges.
--
--   Subtrees of $R(T)$ have Helly number $2$ (Lemma 3.1), which the paper uses to place every vertex of the metric on the computed core (Lemma 5.3).
--
--   **Formalization Note.** A subset is encoded as a subtree when it is nonempty, contains the geodesic between any two of its points, and is closed in the metric of $R(T)$; in a tree, connected subsets are exactly the geodesically convex ones. Geodesics and closedness are taken with unit edge lengths; for a finite tree all positive edge lengths give the same geodesics and the same topology, so the notion depends on the tree only.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §3, p.10 (PDF p.12), footnote 5

import Mathlib
import Definitions.Def_MetricTSPSublinear_rdist

namespace MetricTSPSublinear

variable {m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.IsTree)

/-- The tree `G` with every edge of length `1`. -/
def unitTree : TreeCoverLB.WeightedTree (Fin m) :=
  ⟨G, hG, fun _ => 1, fun _ _ => zero_le_one⟩

/-- The length metric of `R(G)` with every edge of length `1`; it fixes the topology and the geodesics of `R(G)`,
which do not depend on the (positive) edge lengths. -/
noncomputable def unitDist : RPoint G → RPoint G → ℝ :=
  rdist (unitTree G hG)

/-- The geodesic `[p, q]` of `R(G)`: the points `r` with `d(p, r) + d(r, q) = d(p, q)` in the unit length metric,
which in a tree are the points of the path from `p` to `q`. -/
def seg (p q : RPoint G) : Set (RPoint G) :=
  {r | unitDist G hG p r + unitDist G hG r q = unitDist G hG p q}

/-- `X` is closed in `R(G)`: every point outside `X` has a ball around it disjoint from `X`. -/
def IsClosedR (X : Set (RPoint G)) : Prop :=
  ∀ p ∉ X, ∃ r : ℝ, 0 < r ∧ ∀ q, unitDist G hG p q < r → q ∉ X

/-- **A subtree of `R(T)`.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §3, p.10 (PDF p.12): "the subtrees in R(T), which may include parts of the edges", footnote 5:
"which is a closed connected subset of R(T)".

`IsSubtree G hG X` says that `X` is nonempty, contains the geodesic between any two of its points, and is closed.

**Formalization Note.** In a tree a subset is connected exactly when it contains the geodesic between any two of its
points, so "connected" is encoded by geodesic convexity, and "closed" by the metric topology of `R(G)`. Both are
taken with unit edge lengths: for a finite tree every assignment of positive lengths gives the same topology and the
same geodesics, so the notion does not depend on weights (Lemma 3.1 uses none). A subtree is nonempty, as a subtree
of a tree is. -/
def IsSubtree (X : Set (RPoint G)) : Prop :=
  X.Nonempty ∧ (∀ p ∈ X, ∀ q ∈ X, seg G hG p q ⊆ X) ∧ IsClosedR G hG X

end MetricTSPSublinear


