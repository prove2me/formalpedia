-- Prove2me | Definitions.Def_SemiStreamReach_Main_Distances
-- name    : SemiStreamReach_Main_Distances
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:50:53.087752+00:00
-- url     : https://prove2.me/theorems/93d8988c-f42f-4e59-9090-2f7384b9038e
-- title:
--   Weighted directed graphs, distances $\mathrm{dist}$ and $\mathrm{dist}^{(h)}$, unions, induced subgraphs, $TC_w$, $(h,\varepsilon)$-hopsets (Definition 11), rounding $G_\alpha$
-- statement:
--   A **weighted directed graph** on a vertex set $V$ assigns to each ordered pair $(u,v)$ either a nonnegative weight $w(u,v)$ (the edge $(u,v)$ is present) or nothing (no edge). The **length** $w(P)$ of a walk $P=\langle v_0,\dots,v_k\rangle$ is the total weight of its edges and $k$ is its **hop length**. The **distance** $\mathrm{dist}_G(u,v)$ is the least length of a walk from $u$ to $v$ ($\infty$ if $v$ is unreachable from $u$, and $0$ for $u=v$), and $\mathrm{dist}^{(h)}_G(u,v)$ is the least length of a walk from $u$ to $v$ with at most $h$ edges. The **union** $G\cup H$ keeps, for each pair, the lightest of the edges of $G$ and $H$. For $U\subseteq V$, $G[U]$ is the **induced subgraph** (edges with both endpoints in $U$), and the **weighted transitive closure** $TC_w(G[U])$ has an edge $(u,v)$ of weight $\mathrm{dist}_{G[U]}(u,v)$ for every pair $u,v\in U$ with $v$ reachable from $u$ in $G[U]$.
--
--   **Definition 11.** For an integer $h\ge1$ and $\varepsilon\in(0,1)$, a set $H$ of weighted edges is an **$(h,\varepsilon)$-hopset** of $G$ if
--   $$\mathrm{dist}_G(u,v)\ \le\ \mathrm{dist}^{(h)}_{G\cup H}(u,v)\ \le\ (1+\varepsilon)\,\mathrm{dist}_G(u,v)\qquad\text{for all } u,v\in V.$$
--   An edge $(u,v)$ is **noncontracting** in $G$ if its weight is at least $\mathrm{dist}_G(u,v)$. Estimates $\hat d(v)$ are **$(1+\varepsilon)$-approximate distances from $s$** if $\mathrm{dist}_G(s,v)\le\hat d(v)\le(1+\varepsilon)\,\mathrm{dist}_G(s,v)$ for every $v$. For $\alpha>0$, the **rounded graph** $G_\alpha$ gives each edge $e$ the integer weight $\lceil w(e)/\alpha\rceil$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** A graph is `WGraph V := V → V → ℝ≥0∞`, with `⊤` for a missing edge (so at most one edge per ordered pair, nonnegative weights). The union is the pointwise minimum `G ⊓ H`. `dist` and `distH` are infima over vertex lists (walks); for nonnegative weights they equal the minima over paths of the paper. `closureOn G U` is $TC_w(G[U])$ (it includes the zero-weight pairs $(u,u)$, which change no distance). The parameter ranges of Definition 11 ($h\ge1$, $0<\varepsilon<1$) are hypotheses of the statements that use `IsHopset`. `ofEdges E wt` is the graph on `Fin n` with edge set `E` and natural weights `wt`.
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 13 (PDF 15), §3 and Definition 11; p. 3 (PDF 5), TC_w; p. 39 (PDF 41), unions keep the lightest edge

import Mathlib

open scoped ENNReal
open Classical

namespace SemiStreamReach.Main

/-! # Weighted directed graphs, distances, hop-bounded distances and hopsets

Hoppenworth, Li, Mahabadi, Tarnawski, *Semi-Streaming Reachability and Shortest Paths in
n^{1/3+o(1)} Passes*, arXiv:2611.05061 (PDF sha256 c1b64474…), §3 p. 13 (PDF 15): "The length
w(P) of a path P is the total weight of the edges of P. The number of these edges is called the hop
length of P. Let dist_G(u, v) denote the length of a shortest path from u to v in G. The minimum
length of a (u, v)-path with at most h edges is denoted by dist^(h)_G(u, v)." Definition 11 (p. 13),
noncontracting edges (p. 13), (1 + ε)-approximate distances (p. 13), the weighted transitive closure
`TC_w` (p. 3), the rounded graphs `G_α` (p. 13).

**Formalization Note.** A weighted directed graph on a vertex type `V` is a function
`G : V → V → ℝ≥0∞`: `G u v` is the weight of the edge `(u, v)` and `⊤` means there is no such edge;
so there is at most one edge per ordered pair, and weights are nonnegative (every weight in the
paper is nonnegative). The union `G ∪ H` of two graphs keeps the lightest edge of each pair
(p. 39: "As unions keep the lightest edge of each pair"): it is the pointwise minimum `G ⊓ H`.
A walk is a nonempty list of vertices; its weight is the sum of the weights of its consecutive
pairs (`⊤` if one of them is not an edge). `dist G u v` is the infimum over walks from `u` to `v`
and `distH G h u v` the infimum over walks with at most `h` edges; for nonnegative weights these
equal the minima over paths, `dist G u u = 0`, and both are `⊤` exactly when no (short enough) walk
exists. -/

variable {V : Type*}

/-- A weighted directed graph on `V`: `G u v` is the weight of the edge `(u, v)`, `⊤` if absent. -/
abbrev WGraph (V : Type*) := V → V → ℝ≥0∞

/-- The weight of a walk given by its list of vertices: the sum of the weights of its consecutive
pairs. -/
def walkWeight (G : WGraph V) : List V → ℝ≥0∞
  | [] => 0
  | [_] => 0
  | u :: v :: rest => G u v + walkWeight G (v :: rest)

/-- The list `l` is a walk from `u` to `v` (as a vertex sequence; edges are checked by the weight). -/
def IsWalkFrom (u v : V) (l : List V) : Prop :=
  l.head? = some u ∧ l.getLast? = some v

/-- `dist_G(u, v)`: the least weight of a walk from `u` to `v`; `⊤` if `v` is unreachable. -/
noncomputable def dist (G : WGraph V) (u v : V) : ℝ≥0∞ :=
  ⨅ (l : List V) (_ : IsWalkFrom u v l), walkWeight G l

/-- `dist^(h)_G(u, v)`: the least weight of a walk from `u` to `v` with at most `h` edges. -/
noncomputable def distH (G : WGraph V) (h : ℕ) (u v : V) : ℝ≥0∞ :=
  ⨅ (l : List V) (_ : IsWalkFrom u v l) (_ : l.length ≤ h + 1), walkWeight G l

/-- `v` is reachable from `u`, i.e. `(u, v) ∈ TC(G)`. -/
def Reaches (G : WGraph V) (u v : V) : Prop := dist G u v ≠ ⊤

/-- All edge weights are positive. -/
def PositiveWeights (G : WGraph V) : Prop := ∀ u v, 0 < G u v

/-- The induced subgraph `G[U]`: the edges of `G` with both endpoints in `U`. -/
noncomputable def induced (G : WGraph V) (U : Set V) : WGraph V :=
  fun u v => if u ∈ U ∧ v ∈ U then G u v else ⊤

/-- The weighted transitive closure `TC_w(G[U])` of an induced subgraph: an edge `(u, v)` of
weight `dist_{G[U]}(u, v)` for every pair `u, v ∈ U` with `v` reachable from `u` in `G[U]`. -/
noncomputable def closureOn (G : WGraph V) (U : Set V) : WGraph V :=
  fun u v => if u ∈ U ∧ v ∈ U then dist (induced G U) u v else ⊤

/-- Definition 11: `H` is an `(h, ε)`-hopset of `G` if
`dist_G(u, v) ≤ dist^(h)_{G ∪ H}(u, v) ≤ (1 + ε) dist_G(u, v)` for all `u, v`. -/
def IsHopset (G H : WGraph V) (h : ℕ) (ε : ℝ) : Prop :=
  ∀ u v, dist G u v ≤ distH (G ⊓ H) h u v ∧
    distH (G ⊓ H) h u v ≤ ENNReal.ofReal (1 + ε) * dist G u v

/-- Every edge of `H` is noncontracting in `G`: its weight is at least `dist_G(u, v)`. -/
def Noncontracting (G H : WGraph V) : Prop := ∀ u v, dist G u v ≤ H u v

/-- `d` is a vector of `(1 + ε)`-approximate distances from `s` in `G`:
`dist_G(s, v) ≤ d v ≤ (1 + ε) dist_G(s, v)` for every `v` (so `d v = ⊤` exactly when `v` is
unreachable). -/
def IsApproxDist (G : WGraph V) (s : V) (ε : ℝ) (d : V → ℝ≥0∞) : Prop :=
  ∀ v, dist G s v ≤ d v ∧ d v ≤ ENNReal.ofReal (1 + ε) * dist G s v

/-- The ceiling of an extended nonnegative real, `⌈⊤⌉ = ⊤`. -/
noncomputable def ceilE (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else ((⌈x.toReal⌉₊ : ℕ) : ℝ≥0∞)

/-- The rounded graph `G_α`: each edge `e` gets the integer weight `⌈w(e)/α⌉`. -/
noncomputable def rounded (G : WGraph V) (α : ℝ) : WGraph V :=
  fun u v => ceilE (G u v / ENNReal.ofReal α)

/-- The weighted graph on `Fin n` with edge set `E` and natural weights `wt`. -/
noncomputable def ofEdges {n : ℕ} (E : Finset (Fin n × Fin n)) (wt : Fin n × Fin n → ℕ) : WGraph (Fin n) :=
  fun u v => if (u, v) ∈ E then ((wt (u, v) : ℕ) : ℝ≥0∞) else ⊤

end SemiStreamReach.Main


