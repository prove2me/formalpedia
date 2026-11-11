-- Prove2me | Definitions.Def_MinDegST_AddOne_Graph
-- name    : MinDegST_AddOne_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:51:48.334388+00:00
-- url     : https://prove2.me/theorems/0f30a747-d17a-4c8a-813c-7e88c88e034b
-- title:
--   Spanning trees, the optimum Δ⋆, forests, feasibility, slack and saturated nodes
-- statement:
--   Let $G$ be a simple undirected graph on the node set $V=\{0,\dots,n-1\}$. A **spanning tree** of $G$ is a subgraph $T\le G$ on all of $V$ that is a tree. The optimum of the minimum degree spanning tree problem is
--   $$\Delta^\star(G)=\min_{T\ \text{spanning tree of }G}\ \max_{u\in V}\deg_T(u).$$
--   A **forest** $F$ of $G$ is an acyclic subgraph $F\le G$; it contains every node of $G$, so an isolated node is a one-node component, and $f$ denotes its number of components. For a degree threshold $k$ (the paper's $\Delta^\star$), $F$ is **feasible** if $\deg_F(v)\le k+1$ for every $v$; a node $v$ is **slack** if $\deg_F(v)\le k$ and **saturated** if $\deg_F(v)=k+1$. The module also fixes: the statement "$G$ has a spanning tree of maximum degree at most $k$"; the edge list of a graph (each edge exactly once, in either orientation, in any order); the node set $V(P^F_{x,y})$ of the forest path between $x$ and $y$; and $H[C]$, the edges of $H$ with both endpoints in a node set $C$.
--
--   **Formalization Note.** Graphs are `SimpleGraph (Fin n)`. `optDeg G` is `sInf` of the thresholds admitting a spanning tree; for a connected graph this is the minimum, for a disconnected graph the set is empty and the value is $0$ (never used: every statement assumes $G$ connected). `pathVerts F x y` is empty when $x$ and $y$ lie in different components.
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 1 (§1) and p. 35–36 (Part III notation)

import Mathlib

open Classical

namespace MinDegST.AddOne

/-! # Spanning trees, the optimum `Δ⋆`, forests, feasibility, slack and saturated nodes

Bhattacharya, Farokhnejad, Saranurak, Wang, *Faster Algorithms for Minimum Degree Spanning Tree*,
§1 (p. 1) and the notation of Part III (pp. 35–36).

Graphs are simple undirected graphs on the vertex type `Fin n` (`SimpleGraph (Fin n)`). A forest
`F` of `G` is a subgraph `F ≤ G` without cycles; it contains every node of `G`, so isolated nodes
are one-node components. The degree threshold `k` plays the role of `Δ⋆` in Part III; the paper's
own setting is `k = Δ⋆ G`. -/

variable {n : ℕ}

/-- `deg_H(v)`: the number of neighbours of `v` in `H`. -/
noncomputable def deg (H : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => H.Adj v w).card

/-- `T` is a spanning tree of `G`: a subgraph of `G` on all of `Fin n` that is a tree. -/
def IsSpanningTree (G T : SimpleGraph (Fin n)) : Prop :=
  T ≤ G ∧ T.IsTree

/-- `G` has a spanning tree of maximum degree at most `k`. -/
def HasSpanningTreeLE (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ T, IsSpanningTree G T ∧ ∀ v, deg T v ≤ k

/-- `Δ⋆(G) = min_{T spanning tree of G} max_u deg_T(u)` (§1, p. 1). For a connected graph the set
is nonempty and this is a minimum; for a disconnected graph the set is empty and the value is the
junk `0` (every statement of the mission assumes `G` connected). -/
noncomputable def optDeg (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | HasSpanningTreeLE G k}

/-- `F` is a forest of `G`: an acyclic subgraph of `G` (on all nodes of `G`). -/
def IsForestOf (G F : SimpleGraph (Fin n)) : Prop :=
  F ≤ G ∧ F.IsAcyclic

/-- Feasible w.r.t. the threshold `k`: maximum degree at most `k + 1` (p. 35 with `k = Δ⋆`). -/
def Feasible (k : ℕ) (F : SimpleGraph (Fin n)) : Prop :=
  ∀ v, deg F v ≤ k + 1

/-- `v` is slack w.r.t. `F` and the threshold `k`: `deg_F(v) ≤ k` (p. 36 with `k = Δ⋆`). -/
def Slack (k : ℕ) (F : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  deg F v ≤ k

/-- `v` is saturated w.r.t. `F` and the threshold `k`: `deg_F(v) = k + 1` (p. 36). -/
def Saturated (k : ℕ) (F : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  deg F v = k + 1

/-- The number `f` of connected components of `F` (isolated nodes count). -/
noncomputable def numComponents (F : SimpleGraph (Fin n)) : ℕ :=
  Nat.card F.ConnectedComponent

/-- The number `m` of edges of `G`. -/
noncomputable def numEdges (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.card G.edgeSet

/-- `l` lists the edges of `H` exactly once each, each edge as an ordered pair of its endpoints in
either orientation, in any order: every entry is an edge of `H`, no unordered pair repeats, and
every edge of `H` occurs. -/
def IsEdgeListOf (H : SimpleGraph (Fin n)) (l : List (Fin n × Fin n)) : Prop :=
  (∀ p ∈ l, H.Adj p.1 p.2) ∧ (l.map fun p => s(p.1, p.2)).Nodup ∧
    ∀ e ∈ H.edgeSet, e ∈ l.map fun p => s(p.1, p.2)

/-- The `F`-path vertex set `V(P^F_{x,y})`: the nodes on a path of `F` from `x` to `y` (in a forest
this path is unique; empty when `x` and `y` lie in different components). -/
noncomputable def pathVerts (F : SimpleGraph (Fin n)) (x y : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ p : F.Walk x y, p.IsPath ∧ v ∈ p.support

/-- `H[C]`: the edges of `H` with both endpoints in the node set `C`, as a graph on `Fin n` (for
`H = G` this is `E(G[V(C)])`). -/
def inside (H : SimpleGraph (Fin n)) (C : Finset (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => H.Adj a b ∧ a ∈ C ∧ b ∈ C

end MinDegST.AddOne


