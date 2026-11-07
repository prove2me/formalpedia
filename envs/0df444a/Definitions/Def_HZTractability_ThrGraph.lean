-- Prove2me | Definitions.Def_HZTractability_ThrGraph
-- name    : HZTractability_ThrGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:11.630073+00:00
-- url     : https://prove2.me/theorems/1e15721d-7d5b-41d3-98bf-129e46ab4d2a
-- title:
--   Threshold-game graphs, degrees, restriction (2), and $B_2(v)$
-- statement:
--   A **threshold-game graph** is a finite directed graph $G=(V,E)$; write $u\to v$ for $(u,v)\in E$. Self-loops $v\to v$ are allowed. The **indegree** $h_v$ and **outdegree** $o_v$ count the edges into and out of $v$; a self-loop counts once in each.
--
--   **Restriction (2)** requires, at every vertex,
--   $$
--   h_v\in\{0,1,2\},\qquad o_v\in\{1,2\}.
--   $$
--   $B_2(v)$ is the set of vertices at undirected distance at most two from $v$.
--
--   The market $M(G;a,\tau,K)$ is built from such a graph; (2) is the degree condition under which the construction is analysed.
--
--   **Formalization Note** Vertices are $\{0,\dots,n-1\}$ and the edge relation is a Boolean adjacency matrix, so there is at most one edge per ordered pair. "Nonempty" is the separate hypothesis $n\ge 1$.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §2.1, p.6 (PDF p.8), display (2); self-loops §3.1, p.10; B_j(v), App. B, p.38

import Mathlib

namespace HZTractability

/-- **A threshold-game graph** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held version,
sha256 74b7bf9f…, §2.1, p.6 (PDF 8): "a directed graph G = (V, E). Write u → v for (u, v) ∈ E").

The vertex set is `Fin n` and `adj u v = true` means `u → v`. Self-loops `v → v` are allowed (p.10:
"A self-loop contributes one population … it is counted only once").

**Formalization Note** Vertices are `Fin n`; the paper's graphs are finite, and "nonempty" is the
separate hypothesis `1 ≤ G.n`. A directed graph has at most one edge `u → v` for each ordered
pair. -/
structure ThrGraph where
  n : ℕ
  adj : Fin n → Fin n → Bool

namespace ThrGraph

/-- The indegree `h_v = |{u : u → v}|` (§2.1, p.6); a self-loop counts once. -/
def indeg (G : ThrGraph) (v : Fin G.n) : ℕ :=
  (Finset.univ.filter (fun u => G.adj u v = true)).card

/-- The outdegree `o_v = |{t : v → t}|` (§2.1, p.6); a self-loop counts once. -/
def outdeg (G : ThrGraph) (v : Fin G.n) : ℕ :=
  (Finset.univ.filter (fun t => G.adj v t = true)).card

/-- **Restriction (2)** (§2.1, p.6): `h_v ∈ {0, 1, 2}` and `o_v ∈ {1, 2}` at every vertex. -/
def Cond2 (G : ThrGraph) : Prop :=
  ∀ v, G.indeg v ≤ 2 ∧ 1 ≤ G.outdeg v ∧ G.outdeg v ≤ 2

/-- The directed edges `u → v` of `G`, as a finite type. -/
abbrev Edge (G : ThrGraph) : Type :=
  {e : Fin G.n × Fin G.n // G.adj e.1 e.2 = true}

/-- `u` and `w` are adjacent in the underlying undirected graph. -/
def Nbr (G : ThrGraph) (u w : Fin G.n) : Prop :=
  G.adj u w = true ∨ G.adj w u = true

/-- `u ∈ B_2(v)`: `u` is at undirected distance at most two from `v` (App. B, p.38 (PDF 40):
"let B_j(v) contain the vertices at undirected distance at most j from v"). -/
def InB2 (G : ThrGraph) (v u : Fin G.n) : Prop :=
  u = v ∨ G.Nbr u v ∨ ∃ w, G.Nbr u w ∧ G.Nbr w v

end ThrGraph

end HZTractability


