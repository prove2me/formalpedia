-- Prove2me | Definitions.Def_DecrNearAddAPSP_W2_Graphs
-- name    : DecrNearAddAPSP_W2_Graphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:04:45.126834+00:00
-- url     : https://prove2.me/theorems/555b42ce-adae-4f76-83ed-b87011b99d77
-- title:
--   Weighted graphs on Fin n: paths, path weight, W_i, distances, pivots, E_S, clusters, Bernstein's scaled weights
-- statement:
--   A **weighted graph** $G=(V,E,w)$ on a vertex type $\alpha$ is a simple undirected graph together with a weight $w:\binom{\alpha}{2}\to\mathbb N$ on unordered pairs, of which only the values on edges matter. In the paper the vertex set is $V=\{0,\dots,n-1\}$ and weights are positive integers (§5 opens with "each edge $e\in E$ has a positive weight $w(e)>0$"); positivity is stated as a separate predicate, $w(e)\ge 1$ on every edge, and the bound $w(e)\in[1,W]$ likewise.
--
--   For a walk $P$ from $u$ to $v$, its **weight** is $w(P)=\sum_{e\in P}w(e)$ and, for $i\ge1$,
--   $$
--   W_i(P)=\begin{cases}\text{the $i$-th largest entry of the multiset }\{w(e):e\in P\}, & 1\le i\le h(P),\\ 0, & h(P)<i,\end{cases}
--   $$
--   where $h(P)$ is the number of edges of $P$ (p. 2, footnote 1; p. 6). A **path** is a walk with no repeated vertex. The **distance** $\delta_G(u,v)\in\mathbb N\cup\{\infty\}$ is the infimum of $w(P)$ over all walks from $u$ to $v$ ($\infty$ when there is none), and a **shortest path** is a path $\pi$ with $w(\pi)=\delta_G(u,v)$.
--
--   For $S\subseteq V$: $\delta(u,S)=\min_{s\in S}\delta(u,s)$ ($\infty$ for $S=\emptyset$); a **pivot** of $u$ is any $p\in S$ with $\delta(u,p)=\delta(u,S)$ (ties arbitrary); the **hierarchy-induced edge set** is
--   $$
--   E_S(u)=\{(u,v)\in E: w(u,v)<\delta(u,S)\},\qquad E_S=\bigcup_{u\in V}E_S(u)
--   $$
--   (p. 6, strict inequality). $E(v)$ is the set of edges incident to $v$, and $(V,F)$ for a set $F$ of pairs is the subgraph keeping the edges of $G$ in $F$ with $G$'s weights. For the next level $T=S_{i+1}$ of a hierarchy, the **cluster** of $w$ in $G$ is $C_G(w)=\{x\in V:\delta_G(x,w)<\delta_G(x,T)\}$ (Definition 2.1, p. 7), all distances taken in $G$.
--
--   **Bernstein's scaled weights** (§6.1, p. 36): for $\varepsilon>0$, a hop parameter $h$ and a scale $i$, let $\alpha_i=\varepsilon 2^i/h$; an edge of weight $w\le 2^{i+1}$ is kept in $G_i$ with weight $\lceil w/\alpha_i\rceil$, and a walk $p$ has $G_i$-weight $w_{G_i}(p)=\sum_{e\in p}\lceil w(e)/\alpha_i\rceil$.
--
--   These are the objects every statement of the mission is phrased in.
--
--   **Formalization Note** The graph is `WGraph α` (a `SimpleGraph` plus `wt : Sym2 α → ℕ`); paths are Mathlib walks with `IsPath`; distances live in `ℕ∞`, so a disconnected pair has distance `⊤` and no junk value arises. `W_i` sorts the edge weights in non-increasing order and reads entry $i-1$, with default $0$.
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 6, §2; p. 2 footnote 1; p. 7, Definition 2.1; p. 25, §5; p. 36, §6.1

import Mathlib

namespace DecrNearAddAPSP.W2

/-! # Weighted graphs, paths, path weight, `W_i`, distances, hierarchy-induced edge sets, clusters

Koveshi, Roditty, Sapir, *First Near-Additive All-Pairs Approximate Shortest Paths in Decremental
Weighted Graphs*, arXiv:2611.04635 (PDF sha256 6bb2b230…), §2 "Preliminaries", pp. 6–7 (PDF 8–9),
p. 2 footnote 1 (PDF 4), §5 p. 25 (PDF 27).

**Formalization Note.**
* A weighted graph on a vertex type `α` is a simple undirected graph `adj` together with a weight
  `wt : Sym2 α → ℕ` on unordered pairs; only the values on edges matter. Positivity of the weights
  (`w(e) > 0`, §5 p. 25, so `w(e) ≥ 1` for integers) is a hypothesis where the paper assumes it.
* A path from `u` to `v` is a Mathlib walk with `IsPath` (no repeated vertex). Its weight `w(P)` is
  the sum of its edge weights, its hop-length `h(P)` the number of edges, and `W_i(P)` (`i ≥ 1`) the
  `i`-th largest entry of the multiset of its edge weights, `0` when `P` has fewer than `i` edges
  (p. 2 footnote 1).
* `δ_G(u, v) ∈ ℕ ∪ {∞}` is the infimum of the weights of all walks from `u` to `v` (`∞` if none);
  with nonnegative weights this is the minimum over paths.
* `δ(u, S) = min_{s ∈ S} δ(u, s)` (`∞` for `S = ∅`), and `E_S = ⋃_u {(u, v) ∈ E : w(u, v) < δ(u, S)}`
  (p. 6), strict inequality. -/

/-- A weighted undirected graph on `α`: a simple graph `adj` and a weight on unordered pairs. -/
structure WGraph (α : Type) where
  /-- The underlying simple graph. -/
  adj : SimpleGraph α
  /-- The weight of an unordered pair (only its values on edges matter). -/
  wt : Sym2 α → ℕ

namespace WGraph

variable {α : Type}

/-- The weight `w(P)` of a walk: the sum of its edge weights, with multiplicity. -/
def walkWeight (G : WGraph α) {u v : α} (p : G.adj.Walk u v) : ℕ :=
  (p.edges.map G.wt).sum

/-- The weights of the edges of a walk, sorted in non-increasing order. -/
def sortedWeights (G : WGraph α) {u v : α} (p : G.adj.Walk u v) : List ℕ :=
  (p.edges.map G.wt).mergeSort (fun a b => decide (b ≤ a))

/-- `W_i(P)` (p. 2 footnote 1, p. 6): the weight of the `i`-th heaviest edge of `P` for
`1 ≤ i ≤ h(P)`, and `0` if `P` has fewer than `i` edges (also `0` for the unused index `i = 0`). -/
def heavy (G : WGraph α) {u v : α} (p : G.adj.Walk u v) (i : ℕ) : ℕ :=
  if 1 ≤ i then (G.sortedWeights p).getD (i - 1) 0 else 0

/-- The shortest-path distance `δ_G(u, v) ∈ ℕ ∪ {∞}`: the infimum of the weights of all walks from
`u` to `v`, `∞` if there is none. -/
noncomputable def dist (G : WGraph α) (u v : α) : ℕ∞ :=
  ⨅ p : G.adj.Walk u v, (G.walkWeight p : ℕ∞)

/-- `π` is a shortest path from `u` to `v`: a path (no repeated vertex) whose weight is
`δ_G(u, v)`. -/
def IsShortestPath (G : WGraph α) {u v : α} (π : G.adj.Walk u v) : Prop :=
  π.IsPath ∧ (G.walkWeight π : ℕ∞) = G.dist u v

/-- `δ(u, S) = min_{s ∈ S} δ(u, s)`, in `ℕ ∪ {∞}` (`∞` for `S = ∅`). -/
noncomputable def distTo (G : WGraph α) (u : α) (S : Finset α) : ℕ∞ :=
  ⨅ s ∈ S, G.dist u s

/-- `p` is a pivot of `u` in `S` (p. 6): `p ∈ S` and `δ(u, p) = min_{s ∈ S} δ(u, s)` (ties
arbitrary: every minimizer is a pivot). -/
def IsPivot (G : WGraph α) (S : Finset α) (u p : α) : Prop :=
  p ∈ S ∧ ∀ s ∈ S, G.dist u p ≤ G.dist u s

/-- Every edge weight is positive (§5, p. 25: `w(e) > 0`). -/
def PosWeights (G : WGraph α) : Prop :=
  ∀ e ∈ G.adj.edgeSet, 1 ≤ G.wt e

/-- Every edge weight is an integer in `[1, W]`. -/
def WeightsIn (G : WGraph α) (W : ℕ) : Prop :=
  ∀ e ∈ G.adj.edgeSet, 1 ≤ G.wt e ∧ G.wt e ≤ W

/-- The subgraph `(V, F)` for a set `F` of pairs: the edges of `G` that lie in `F`, with `G`'s
weights. -/
def restrict (G : WGraph α) (F : Set (Sym2 α)) : WGraph α :=
  ⟨SimpleGraph.fromEdgeSet (F ∩ G.adj.edgeSet), G.wt⟩

/-- `E(v)`: the edges of `G` incident to `v` (p. 6). -/
def incident (G : WGraph α) (v : α) : Set (Sym2 α) :=
  {e | e ∈ G.adj.edgeSet ∧ v ∈ e}

/-- `E_S(u) = {(u, v) ∈ E : w(u, v) < δ(u, S)}` (p. 6), as unordered pairs. -/
noncomputable def hierEdgesAt (G : WGraph α) (S : Finset α) (u : α) : Set (Sym2 α) :=
  {e | ∃ v, e = s(u, v) ∧ G.adj.Adj u v ∧ (G.wt s(u, v) : ℕ∞) < G.distTo u S}

/-- The hierarchy-induced edge set `E_S = ⋃_{u ∈ V} E_S(u)` (p. 6). -/
noncomputable def hierEdges (G : WGraph α) (S : Finset α) : Set (Sym2 α) :=
  ⋃ u, G.hierEdgesAt S u

/-- The cluster `C_G(w) = {x ∈ V : δ_G(x, w) < δ_G(x, T)}` of `w` with respect to the next level
`T = S_{i+1}` of the hierarchy (Definition 2.1, p. 7), every distance taken in `G`. -/
noncomputable def cluster (G : WGraph α) (T : Finset α) (w : α) : Set α :=
  {x | G.dist x w < G.distTo x T}

end WGraph

/-- Bernstein's scaled weight (§6.1, p. 36): for a hop parameter `h` and `ε > 0`, scale `i` uses
`α_i = ε·2^i/h`; an edge of weight `w ≤ 2^{i+1}` is kept in `G_i`, its weight rounded up to the
nearest integer multiple of `α_i` and divided by `α_i`, which gives `⌈w/α_i⌉`. -/
noncomputable def scaledWeight (ε : ℝ) (h i w : ℕ) : ℤ :=
  ⌈(w : ℝ) / (ε * 2 ^ i / h)⌉

/-- The weight `w_{G_i}(p) = Σ_{e ∈ p} ⌈w(e)/α_i⌉` of a walk in the scaled graph `G_i` (§6.1). -/
noncomputable def scaledWalkWeight {α : Type} (G : WGraph α) (ε : ℝ) (h i : ℕ) {u v : α}
    (p : G.adj.Walk u v) : ℤ :=
  (p.edges.map fun e => scaledWeight ε h i (G.wt e)).sum

end DecrNearAddAPSP.W2


