-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_supp
-- name    : EulerSparsify_DiGraph_supp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:23.193371+00:00
-- url     : https://prove2.me/theorems/ae68fec4-47e4-4b45-aeb8-3cf1ad9171cb
-- title:
--   The support graph $(V,\mathrm{supp}(w),w_{\mathrm{supp}(w)})$ and simple directed graphs
-- statement:
--   For a weighted directed graph $\vec G=(V,E,w)$, the **support graph** $(V,\mathrm{supp}(w),w_{\mathrm{supp}(w)})$ has the same vertices, the edges of nonzero weight, and their weights; Algorithm 5.1 takes a nested ER partitioning of this graph as input. A directed graph is **simple** if it has no self-loops and no two edges with the same head and the same tail (antiparallel edges are allowed).
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Algorithm 5.1, line 1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph

namespace EulerSparsify

/-- The support `supp(w)` of the weights: the edges of nonzero weight. -/
noncomputable def DiGraph.suppEdges {V E : Type} [Fintype E] (G : DiGraph V E) : Finset E :=
  Finset.univ.filter fun e => G.w e ≠ 0

/-- **The graph `(V, supp(w), w_supp(w))`** (Algorithm 5.1, line 1, p.22, PDF p.24).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Algorithm 5.1: "Input: a simple ⃗G = (V, E, w) and {K_i, F_i, b_i}_{i∈[I]} is a ρ-nested ER
partitioning of (V, supp(w), w_supp(w))".

The graph on the same vertices whose edges are the edges of nonzero weight, with their weights. -/
def DiGraph.supp {V E : Type} [Fintype E] (G : DiGraph V E) : DiGraph V G.suppEdges where
  head e := G.head e
  tail e := G.tail e
  w e := G.w e

/-- **Simple directed graph** (Algorithm 5.1, line 1, p.22): no self-loops and no two edges with the
same head and the same tail. -/
def DiGraph.IsSimple {V E : Type} (G : DiGraph V E) : Prop :=
  (∀ e, G.head e ≠ G.tail e) ∧ ∀ e f, G.head e = G.head f → G.tail e = G.tail f → e = f

end EulerSparsify


