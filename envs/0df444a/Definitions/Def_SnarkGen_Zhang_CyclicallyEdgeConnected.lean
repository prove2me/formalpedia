-- Prove2me | Definitions.Def_SnarkGen_Zhang_CyclicallyEdgeConnected
-- name    : SnarkGen_Zhang_CyclicallyEdgeConnected
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:20.395577+00:00
-- url     : https://prove2.me/theorems/14c1966f-a424-464f-a9b5-03d3fde3df8d
-- title:
--   Cyclically $k$-edge connected graphs (Section 2)
-- statement:
--   Let $G$ be a simple graph and $k$ a natural number. The graph $G$ is **cyclically $k$-edge connected** if the deletion of fewer than $k$ edges from $G$ does not create two components both of which contain at least one cycle.
--
--   Precisely: for every finite set $S$ of edges of $G$ with
--   $$
--   |S| < k,
--   $$
--   any two connected components of the graph $G - S$ that each contain a cycle (of $G - S$) are the same component.
--
--   For cubic graphs ordinary edge connectivity is at most $3$, since the three edges at a vertex separate it, but such a cut leaves a single vertex with no cycle. Cyclic edge connectivity ignores those trivial cuts. It measures how hard it is to split a graph into two parts that both carry cycles, and snarks are required to be cyclically $4$-edge connected so that they do not decompose into smaller uncolourable pieces.
--
--   **Formalization Note** The edge set $S$ is a `Finset (Sym2 V)` contained in the edge set of $G$. Components and cycles are taken in `G.deleteEdges S`. A component "contains a cycle" when some vertex of it carries a closed walk that is a cycle (`Walk.IsCycle`) in `G.deleteEdges S`. The vertex type is arbitrary; no finiteness is needed for the definition.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 4, Section 2

import Mathlib

namespace SnarkGen.Zhang

/-- `G` is *cyclically `k`-edge connected* (p. 4): deleting fewer than `k` edges of `G` never
leaves two distinct connected components that each contain a cycle. Components and cycles are
those of the graph `G.deleteEdges S` obtained after the deletion. -/
def CyclicallyEdgeConnected {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset (Sym2 V), (↑S : Set (Sym2 V)) ⊆ G.edgeSet → S.card < k →
    ∀ c₁ c₂ : (G.deleteEdges ↑S).ConnectedComponent,
      (∃ v ∈ c₁.supp, ∃ p : (G.deleteEdges ↑S).Walk v v, p.IsCycle) →
      (∃ v ∈ c₂.supp, ∃ p : (G.deleteEdges ↑S).Walk v v, p.IsCycle) →
      c₁ = c₂

end SnarkGen.Zhang


