-- Prove2me | Definitions.Def_ARTreeCover_Supplement_IsBalancedSep
-- name    : ARTreeCover_Supplement_IsBalancedSep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:59:49.843915+00:00
-- url     : https://prove2.me/theorems/0b9ab600-e144-470d-b488-2ccd0bc82bc0
-- title:
--   Sub-graphs of a weighted graph and balanced vertex separators
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph. A **sub-graph** of $G$ is a pair $(U,G')$ consisting of a vertex set $U\subseteq V$ and a set $E(G')$ of edges of $G$ with both endpoints in $U$, each edge keeping its weight $w$.
--
--   For a graph with vertex set $U$ and edge set $H$, a set $S$ is a **balanced vertex separator** (Definition 4) if $S\subseteq U$ and every connected component of the graph $H[U\setminus S]$ has at most $|U|/2$ vertices.
--
--   These two notions underlie vertex-separability (Definition 5) and path-separability (Definition 6), which are hereditary: they ask for a separator in every sub-graph.
--
--   **Formalization Note** A sub-graph is a weighted graph $G'$ on the same vertex type whose edges are edges of $G$ inside $U$ with $G$'s weights; vertices outside $U$ are isolated in $G'$ and ignored. The component of $x\in U\setminus S$ is the set of vertices reachable from $x$ by a walk of $H$ inside $U\setminus S$, and "at most $|U|/2$ vertices" is $2\,|\text{component}|\le|U|$.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 4, p.10 (PDF p.13); Definitions 5–6, pp.10–11 (PDF pp.13–14)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

namespace ARTreeCover.Supplement

open ARTreeCover

/-- `IsSubgraph G U G'`: the pair `(U, G')` is a sub-graph of the weighted graph `G`, with vertex
set `U ⊆ V` and edge set `E(G') ⊆ E(G[U])`, each edge keeping its weight in `G`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 5 and Definition 6, pp.10–11
(PDF pp.13–14): "every sub-graph of G".

**Formalization Note.** The sub-graph is recorded as a weighted graph `G'` on the same vertex type
`V`, all of whose edges are edges of `G` between vertices of `U` and carry `G`'s weight; the
vertices of `V` outside `U` are isolated in `G'` and are not vertices of the sub-graph. -/
def IsSubgraph {V : Type} (G : WGraph V) (U : Set V) (G' : WGraph V) : Prop :=
  G'.graph ≤ G.graph ∧ (∀ x y, G'.graph.Adj x y → x ∈ U ∧ y ∈ U) ∧
    ∀ e ∈ G'.graph.edgeSet, G'.w e = G.w e

/-- `IsBalancedSep H U S`: `S` is a balanced vertex separator of the graph with vertex set `U` and
edge set `H` (Definition 4, p.10, PDF p.13): `S ⊆ U` and every connected component of
`H[U ∖ S]` has at most `|U|/2` vertices.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 4, p.10 (PDF p.13): "a balanced
vertex separator, or shortly, a separator, is a subset S ⊆ V such that each connected component of
the graph G′ = G[V \ S] contains at most n/2 vertices."

**Formalization Note.** The component of `x ∈ U ∖ S` is the set of `y` joined to `x` by a walk of
`H` all of whose vertices lie in `U ∖ S`; "at most `|U|/2` vertices" is `2 · |component| ≤ |U|`
(`Set.ncard`, finite on a finite vertex type). -/
def IsBalancedSep {V : Type} (H : SimpleGraph V) (U S : Set V) : Prop :=
  S ⊆ U ∧ ∀ x ∈ U \ S,
    2 * {y | ∃ p : H.Walk x y, ∀ z ∈ p.support, z ∈ U \ S}.ncard ≤ U.ncard

end ARTreeCover.Supplement


