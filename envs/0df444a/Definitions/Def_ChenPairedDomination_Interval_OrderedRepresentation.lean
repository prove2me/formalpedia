-- Prove2me | Definitions.Def_ChenPairedDomination_Interval_OrderedRepresentation
-- name    : ChenPairedDomination_Interval_OrderedRepresentation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T01:25:45.987098+00:00
-- url     : https://prove2.me/theorems/bc64fab2-35ba-4d26-b002-cbd3765b9ccb
-- title:
--   An interval representation with the supplied left-endpoint order
-- statement:
--   An ordered representation of a simple graph on Fin n supplies real left and right endpoints for each vertex, with left at most right, such that distinct vertices are adjacent exactly when their closed intervals intersect. The left endpoints are nondecreasing in the vertex index. Equal endpoints, equal left endpoints, equal intervals and point intervals are allowed. No connectivity, minimum interval length or proper-interval condition is imposed. Forgetting the order gives AppliedComb.Graphs.IsIntervalGraph, the imported general interval-graph predicate. Vertex index 0 represents the paper’s first vertex.
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, §3, pp. 9, 11

import Definitions.Def_AppliedComb_Graphs_IsIntervalGraph

namespace ChenPairedDomination.Interval

/-- A supplied closed-real-interval representation, with the supplied left-endpoint order. -/
structure OrderedRepresentation {n : ℕ} (G : SimpleGraph (Fin n)) where
  left : Fin n → ℝ
  right : Fin n → ℝ
  nonempty : ∀ v, left v ≤ right v
  represents : ∀ u v, u ≠ v →
    (G.Adj u v ↔ (Set.Icc (left u) (right u) ∩ Set.Icc (left v) (right v)).Nonempty)
  ordered : Monotone left

/-- Forgetting the supplied order and witnesses gives the published general object. -/
theorem OrderedRepresentation.intervalGraph {n : ℕ} {G : SimpleGraph (Fin n)}
    (R : OrderedRepresentation G) : AppliedComb.Graphs.IsIntervalGraph G :=
  ⟨R.left, R.right, R.nonempty, R.represents⟩

end ChenPairedDomination.Interval


