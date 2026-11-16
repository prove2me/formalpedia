-- Prove2me | Definitions.Def_ARTreeCover_Supplement_HasPathSep
-- name    : ARTreeCover_Supplement_HasPathSep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:01:09.667002+00:00
-- url     : https://prove2.me/theorems/e68b3250-9908-48da-a441-263a01d58861
-- title:
--   Path separators; weakly $p$-path-separable and $(\ell,\pi)$-path-separable graphs, tree-like variants
-- statement:
--   Let $G'$ be a weighted graph with vertex set $U$. A **path separator** of $G'$ with $\ell$ rounds and counts $p_0,\dots,p_{\ell-1}$ is a balanced vertex separator of the form
--   $$S=P_0\cup P_1\cup\dots\cup P_{\ell-1},$$
--   where each $P_i$ is the union of the vertex sets of $p_i$ shortest paths of the graph $H_i=G'\setminus\bigcup_{j<i}P_j$ (that is, $G'$ with the vertices of the earlier rounds removed). A shortest path of $H_i$ is a path all of whose vertices lie in $H_i$ and whose weight equals the distance $d_{H_i}$ between its endpoints. The separator is **tree-like** if, for every $i$, the paths forming $P_i$ share a common endpoint $r_i$.
--
--   Following Definition 6, a graph $G$ is
--
--   1. **(weakly) $p$-path-separable** if every sub-graph of $G$ has a path separator with $\sum_i p_i\le p$;
--   2. **(weakly) $(\ell,\pi)$-path-separable** if every sub-graph of $G$ has a path separator with $\ell$ rounds and $p_i\le\pi$ for every $0\le i<\ell$;
--   3. **tree-like** $p$- or $(\ell,\pi)$-path-separable if moreover the separators can be taken tree-like.
--
--   Planar graphs, bounded-genus graphs and $H$-minor-free graphs are path-separable (Theorem 8, cited); the supplement's Theorems 16, 18, 21, 25, 26, 39 and 40 hold for these classes.
--
--   **Formalization Note** Sub-graphs are arbitrary vertex subsets with arbitrary subsets of the induced edges (weights inherited). A round with $p_i=0$ is empty, so "exactly $\ell$ rounds" and "at most $\ell$ rounds" agree. In the tree-like case the common endpoint is recorded as the first endpoint of each path (paths are undirected). The strongly path-separable variant (item 2 of Definition 6) is not used by any theorem of the supplement and is not defined.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 6, p.11 (PDF p.14)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_Supplement_IsBalancedSep

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- `IsShortestPathSet G W P root`: `P` is the vertex set of a shortest path of the graph
`G[W]` (the weighted graph `G` with the vertices outside `W` removed), and, if `root = some r`,
the path has `r` as an endpoint.

A shortest path is a path (a walk without repeated vertices) from `x` to `y`, all of whose
vertices lie in `W`, whose weight equals `d_{G[W]}(x, y)`. A single vertex is a shortest path
(of weight `0`). -/
def IsShortestPathSet {V : Type} (G : WGraph V) (W : Set V) (P : Set V) (root : Option V) :
    Prop :=
  ∃ (x y : V) (p : G.graph.Walk x y), p.IsPath ∧ (∀ z ∈ p.support, z ∈ W) ∧
    G.walkWeight p = G.distIn W x y ∧ P = {z | z ∈ p.support} ∧ (root = none ∨ root = some x)

/-- `HasPathSep G U ℓ c tree`: the graph with vertex set `U` and weighted edge set `G` has a
balanced vertex separator of the form `P₀ ∪ P₁ ∪ ⋯ ∪ P_{ℓ−1}` where each `P_i` is a union of `c i`
shortest paths of `H_i = G[U ∖ ⋃_{j<i} P_j]`; if `tree = true`, the paths forming `P_i` share a
common endpoint `r_i ∈ V`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 6, p.11 (PDF p.14): "every
sub-graph G′ of a graph G has a balanced vertex separator of the form P0 ∪ P1 ∪ · · · ∪ Pℓ−1, where
Pi is a union of pi shortest paths in the graph Hi = G′ \ ⋃_{j<i} Pj (i.e., G′ with the vertices of
⋃_{j<i} Pj removed)"; item 4: "the paths that form Pi share a common endpoint ri ∈ V".

**Formalization Note.** `Q i j` (`j < c i`) is the vertex set of the `j`-th path of round `i`;
`c i = 0` gives `P_i = ∅`. With `tree = true` every path of round `i` has the common endpoint
`r_i` (recorded as `ρ = some r_i`) as its first endpoint (paths are undirected); with
`tree = false`, `ρ = none` imposes nothing. -/
def HasPathSep {V : Type} (G : WGraph V) (U : Set V) (ℓ : ℕ) (c : Fin ℓ → ℕ) (tree : Bool) :
    Prop :=
  ∃ Q : (i : Fin ℓ) → Fin (c i) → Set V,
    (∀ i, ∃ ρ : Option V, ∀ j,
      IsShortestPathSet G (U \ ⋃ (i' : Fin ℓ) (_ : i' < i), ⋃ j', Q i' j') (Q i j) ρ ∧
        (tree = true → ρ ≠ none)) ∧
    IsBalancedSep G.graph U (⋃ i, ⋃ j, Q i j)

/-- `IsPPathSeparable G p tree`: `G` is (weakly) `p`-path-separable (`tree = false`), resp.
(weakly) tree-like `p`-path-separable (`tree = true`): every sub-graph `G'` of `G` has a separator
as in `HasPathSep` with `∑_{i<ℓ} p_i ≤ p` (any number `ℓ` of rounds).

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 6, items 1 and 4, p.11 (PDF p.14):
"We say that G is (weakly) p-path-separable if ∑_{i=0}^{ℓ−1} pi ≤ p."; "p-path-separable" without a
qualifier means weakly.

**Formalization Note.** Sub-graphs are `IsSubgraph` (any vertex subset `U`, any subset of the edges
of `G[U]`, weights inherited); the separator is balanced with respect to `|U|`. -/
def IsPPathSeparable {V : Type} (G : WGraph V) (p : ℕ) (tree : Bool) : Prop :=
  ∀ (U : Set V) (G' : WGraph V), IsSubgraph G U G' →
    ∃ (ℓ : ℕ) (c : Fin ℓ → ℕ), ∑ i, c i ≤ p ∧ HasPathSep G' U ℓ c tree

/-- `IsLPiPathSeparable G ℓ π tree`: `G` is (weakly) `(ℓ, π)`-path-separable (`tree = false`),
resp. (weakly) tree-like `(ℓ, π)`-path-separable (`tree = true`): every sub-graph `G'` of `G` has a
separator `P₀ ∪ ⋯ ∪ P_{ℓ−1}` as in `HasPathSep` with `p_i ≤ π` for every `0 ≤ i < ℓ`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 6, items 3 and 4, p.11 (PDF p.14):
"We say that G is (weakly) (ℓ, π)-path-separable if pi ≤ π for every 0 ≤ i < ℓ."

**Formalization Note.** The separator has exactly `ℓ` rounds; since a round may be empty
(`p_i = 0`), this is the same as at most `ℓ` rounds. -/
def IsLPiPathSeparable {V : Type} (G : WGraph V) (ℓ π : ℕ) (tree : Bool) : Prop :=
  ∀ (U : Set V) (G' : WGraph V), IsSubgraph G U G' →
    ∃ c : Fin ℓ → ℕ, (∀ i, c i ≤ π) ∧ HasPathSep G' U ℓ c tree

end ARTreeCover.Supplement


