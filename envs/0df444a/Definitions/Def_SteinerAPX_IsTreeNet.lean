-- Prove2me | Definitions.Def_SteinerAPX_IsTreeNet
-- name    : SteinerAPX_IsTreeNet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:01.491021+00:00
-- url     : https://prove2.me/theorems/1663f1f1-3057-4ea4-8dc0-fba7e3bfdd57
-- title:
--   Trees of line segments
-- statement:
--   A network $N$ (a finite set of segments in a real inner product space) is a **tree of line segments** if
--
--   1. every segment is nondegenerate ($a\neq b$);
--   2. two distinct segments meet at most in a common endpoint;
--   3. the graph whose vertices are the endpoints of the segments and whose edges are the segments is a tree (connected and acyclic).
--
--   The cables $\Gamma_i$ of the cable reduction are trees of line segments, and so are the recovered trees $T_i$ of the cable-recovery lemma; the tree property is what makes "the length of $T_i$ is at least the length of $\Gamma_i$" meaningful in the proof of Lemma 8.
--
--   **Formalization Note** Condition 2 excludes a segment listed twice and segments that cross or touch away from their endpoints, so the carrier is the geometric realization of the endpoint graph. The empty network is not a tree.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.1, p.13 (PDF p.15) ("a tree of line segments, the cable Γi"); Lemma 8, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_SteinerAPX_Network

namespace SteinerAPX

/-- **Trees of line segments.** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC
2027 submission (manuscript sha256 6f78a9ea…), §4.1, p.13 (PDF p.15): "For each label i, we join
the ports labelled i by a tree of line segments, the cable Γi"; also the trees `Tᵢ` of Lemma 8,
p.16.

A network is a tree of line segments when its segments are nondegenerate, two distinct segments
meet at most in a common endpoint, and the graph whose vertices are the segment endpoints and whose
edges are the segments is a (connected, acyclic) tree.

**Formalization Note** The condition on intersections excludes a segment listed twice (also in
reverse) and two segments crossing or touching away from their endpoints, so the carrier is the
geometric realization of the endpoint graph. The empty network has no vertices and is not a tree. -/
def IsTreeNet {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (N : Network V) : Prop :=
  (∀ e ∈ N, e.1 ≠ e.2) ∧
  (∀ e ∈ N, ∀ e' ∈ N, e ≠ e' →
    segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆ ({e.1, e.2} : Set V) ∩ {e'.1, e'.2}) ∧
  ((SimpleGraph.fromEdgeSet {s : Sym2 V | ∃ e ∈ N, s = s(e.1, e.2)}).induce
      {v : V | ∃ e ∈ N, v = e.1 ∨ v = e.2}).IsTree

end SteinerAPX


