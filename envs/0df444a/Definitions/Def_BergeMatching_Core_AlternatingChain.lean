-- Prove2me | Definitions.Def_BergeMatching_Core_AlternatingChain
-- name    : BergeMatching_Core_AlternatingChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:50.928608+00:00
-- url     : https://prove2.me/theorems/c75db361-9751-48f2-bb6d-b64ea323cf2e
-- title:
--   Matchings: neutral points, maximum matchings, alternating chains, maximum stable sets and minimum covers
-- statement:
--   Let $G = (X, U)$ be a finite simple graph with vertex set $X$ and edge set $U$, and let $V_0 \subseteq U$ be a **matching**, that is, a set of edges no two of which share a vertex. The edges of $V_0$ are called **strong**, all other edges **weak**.
--
--   1. A vertex $x$ is **neutral** if no strong edge contains $x$. The set of neutral points is $N$.
--   2. A matching $V_0$ is **maximum** if
--   $$
--   |V| \le |V_0| \quad \text{for every matching } V \text{ of } G .
--   $$
--   This is maximality of the number of edges, not maximality under inclusion.
--   3. Given any set $S$ of edges declared strong (for a graph $H$, not necessarily $G$), a walk in $H$ is **alternating with respect to $S$** if it does not use the same edge twice and, of any two consecutive edges of the walk, one lies in $S$ and the other does not. Vertices may be repeated.
--   4. An **alternating chain** of $G$ (with respect to $V_0$) is a walk of $G$ that is alternating with respect to $S = V_0$.
--   5. A set $A \subseteq X$ is **internally stable** if no edge joins two vertices of $A$; it is a **maximum internally stable set** if $|B| \le |A|$ for every internally stable $B$.
--   6. A set $C \subseteq X$ is a **cover** if every edge has at least one endpoint in $C$; it is a **minimum cover** if $|C| \le |D|$ for every cover $D$.
--
--   These are the objects of Berge's characterization of maximum matchings: alternating chains joining two neutral points are exactly the obstructions to maximality.
--
--   **Formalization Note** The graph is a Mathlib `SimpleGraph V` and the matching is a subgraph `M : G.Subgraph` with `M.IsMatching`; its edges are `M.edgeSet` and its size is `M.edgeSet.ncard`. "Does not use the same edge twice" is `Walk.IsTrail`, and alternation is imposed on consecutive edges of the walk (`List.IsChain`). The alternation predicate is stated for an arbitrary edge set so that it also serves the auxiliary graph $\bar G$. Internally stable sets and covers are Mathlib's `IsIndepSet` and `IsVertexCover`; the three optimum predicates require a finite vertex type so that `Set.ncard` is the true cardinality. The paper's "unoriented graph (or 1-dimensional regular complex)" may have parallel edges; a matching uses at most one edge of each parallel class, so simple graphs lose nothing for the results stated here.
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), p. 842, Introduction (Problems 1–3) and The Theorems, first paragraph

import Mathlib

namespace BergeMatching.Core

/-- Berge (1957), p. 842. Given a matching `V₀` of `G`, encoded as a subgraph `M` with
`M.IsMatching`, the edges of `M` are *strong* and all other edges are *weak*. A vertex `x` is
*neutral* if it is not adjacent to a strong edge, i.e. no edge of `M` contains `x`. -/
def IsNeutral {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (x : V) : Prop :=
  ∀ e ∈ M.edgeSet, x ∉ e

/-- A *maximum* matching (Problem 3, p. 842): a matching whose number of edges is at least that
of every matching of `G`. This is cardinality-maximum, not inclusion-maximal. -/
def IsMaximumMatching {V : Type} [Finite V] {G : SimpleGraph V} (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard

/-- Alternation relative to an arbitrary set `S` of strong edges (p. 842): the chain `p` does
not use the same edge twice (`p.IsTrail`), and of any two consecutive edges of `p` one is in `S`
(strong) and the other is not (weak). Stated for any graph `H`, so that it serves both `G` and
the auxiliary graph `Ḡ`. -/
def IsAlternatingWrt {W : Type} {H : SimpleGraph W} (S : Set (Sym2 W)) {u v : W}
    (p : H.Walk u v) : Prop :=
  p.IsTrail ∧ p.edges.IsChain (fun e e' => (e ∈ S ↔ e' ∉ S))

/-- An *alternating chain* of `G` with respect to the matching `M` (p. 842): a walk of `G`
that uses no edge twice and whose consecutive edges alternate between edges of `M` and edges
not in `M`. Vertices may repeat. -/
def IsAlternatingChain {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {u v : V}
    (p : G.Walk u v) : Prop :=
  IsAlternatingWrt M.edgeSet p

/-- A *maximum internally stable set* (Problem 1, p. 842): an independent set of `G` with at
least as many elements as every independent set of `G`. -/
def IsMaximumIndepSet {V : Type} [Finite V] (G : SimpleGraph V) (A : Set V) : Prop :=
  G.IsIndepSet A ∧ ∀ B : Set V, G.IsIndepSet B → B.ncard ≤ A.ncard

/-- A *minimum cover* (Problem 2, p. 842): a vertex cover of `G` (every edge has an endpoint in
it) with at most as many elements as every vertex cover of `G`. -/
def IsMinimumVertexCover {V : Type} [Finite V] (G : SimpleGraph V) (C : Set V) : Prop :=
  G.IsVertexCover C ∧ ∀ D : Set V, G.IsVertexCover D → C.ncard ≤ D.ncard

end BergeMatching.Core


