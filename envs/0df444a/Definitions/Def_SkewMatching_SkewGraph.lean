-- Prove2me | Definitions.Def_SkewMatching_SkewGraph
-- name    : SkewMatching_SkewGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:07:43.644702+00:00
-- url     : https://prove2.me/theorems/e41e2538-ae7d-4581-9a43-97a857610555
-- title:
--   Definition 3 — skew-symmetric multigraphs at unit capacity
-- statement:
--   A **skew-symmetric graph** is a directed multigraph with a vertex set $V$, an edge set $E$, tail and head maps, and a map $\sigma$ on vertices and on edges such that $\sigma(x)\ne x$ and $\sigma(\sigma(x))=x$ for every vertex and edge $x$, and such that for an edge $e=(u,v)$ the symmetric edge $\sigma(e)$ goes from $\sigma(v)$ to $\sigma(u)$.
--
--   The graph is **simple** if it has no parallel edges, that is, an edge is determined by its tail and head. A **sub-multigraph** is a set of edges closed under $\sigma$.
--
--   This is the object the whole mission works on: residual graphs and the sampled subgraph $H$ are multigraphs, so edges form a type, and simplicity is a separate condition.
--
--   **Formalization Note** The paper's Definition 3 has positive integer capacities $c_e$ with $c_e=c_{\sigma(e)}$; §2.3 then states that all graphs are of unit capacity, so no capacity field is present.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Definition 3, pp.2–3; §2.3, p.4; 'no parallel edges', p.1

import Mathlib

namespace SkewMatching

/-- **Definition 3 (Skew-symmetric graphs)**, pp.2–3, at unit capacity (§2.3, p.4): a directed multigraph
with an edge type `E`, `tail` and `head`, and a fixed-point-free involution `σ` on vertices and on edges,
with `σ(e)` an edge from `σ(head e)` to `σ(tail e)`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…), Definition 3, pp.2–3; §2.3, p.4.

**Formalization Note.** "All graphs in this paper are simple and of unit capacity" (§2.3, p.4), so no
capacity field exists. Residual graphs are multigraphs, so edges are a type and `Simple` is a separate
predicate. Sub-multigraphs are `σ`-closed finite sets of edges (`SymmClosed`). Finiteness is a hypothesis
of each theorem. -/
structure SkewGraph (V E : Type*) where
  tail : E → V
  head : E → V
  σV : V → V
  σE : E → E
  σV_invol : Function.Involutive σV
  σV_ne : ∀ v, σV v ≠ v
  σE_invol : Function.Involutive σE
  σE_ne : ∀ e, σE e ≠ e
  tail_σE : ∀ e, tail (σE e) = σV (head e)
  head_σE : ∀ e, head (σE e) = σV (tail e)

namespace SkewGraph

variable {V E : Type*} (G : SkewGraph V E)

/-- **Simple** (p.1): "graphs with no parallel edges between any two vertices". An edge is determined by
its tail and head. -/
def Simple : Prop := Function.Injective fun e => (G.tail e, G.head e)

/-- A sub-multigraph: a set of edges closed under `σ`. -/
def SymmClosed (H : Finset E) : Prop := ∀ e ∈ H, G.σE e ∈ H

end SkewGraph

end SkewMatching


