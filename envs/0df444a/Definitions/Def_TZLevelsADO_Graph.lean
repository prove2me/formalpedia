-- Prove2me | Definitions.Def_TZLevelsADO_Graph
-- name    : TZLevelsADO_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:56.789322+00:00
-- url     : https://prove2.me/theorems/96adee84-c726-470e-b488-a3c8c7ebb79b
-- title:
--   Weighted undirected graphs as edge lists, walks, and shortest-path distances
-- statement:
--   A **weighted undirected graph** with $n$ vertices and $m$ edges is given as an edge list: the vertices are $0, 1, \dots, n-1$, and edge $e \in \{0, \dots, m-1\}$ joins the vertices $\mathrm{src}(e)$ and $\mathrm{dst}(e)$ and has weight $\ell(e) \in \mathbb R$. The graph has **positive weights** if $\ell(e) > 0$ for every edge.
--
--   Each edge $e$ has two **orientations**, $(\mathrm{src}(e), \mathrm{dst}(e))$ and $(\mathrm{dst}(e), \mathrm{src}(e))$. A **walk** from $u$ to $v$ is a finite sequence of oriented edges in which the first starts at $u$, each starts where the previous one ends, and the last ends at $v$ (the empty walk goes from $u$ to $u$). Its **length** is the sum of the weights of its edges. The graph is **connected** if it has at least one vertex and any two vertices are joined by a walk.
--
--   The **distance** $d(u, v)$ is the infimum of the lengths of the walks from $u$ to $v$, and a **shortest path** $P(u, v)$ is a walk from $u$ to $v$ of length $d(u, v)$.
--
--   These are the graph conventions of §2 of the paper (connected, positive real weights, oriented edges); every statement of the mission is about such graphs.
--
--   **Formalization Note** Parallel edges and loops are allowed, which is more general than a graph $G = (V, E)$. For connected graphs with positive weights the infimum is attained and is the usual shortest-path distance; the junk value of an empty infimum never occurs under these assumptions. With positive weights a shortest walk repeats no vertex.
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), §2 Preliminaries, pp.6–7 (PDF pp.7–8)

import Mathlib

namespace TZLevelsADO

/-!
# Weighted undirected graphs, walks and distances

S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels: new tools for the
Thorup–Zwick hierarchy and their applications*, arXiv:2611.01297 (held file sha256 dfeca900…),
§2 "Preliminaries", pp.6–7 (PDF pp.7–8): "Let G = (V, E) be an undirected graph with n = |V| vertices
and m = |E| edges. … weighted graphs with positive real edge weights. … Each edge {x, y} ∈ E has two
orientations, (x, y) and (y, x), and we refer to them as oriented edges. We assume that G is connected,
so all distances are finite. … The distance d(u, v) between u and v is the length of a shortest path
between u and v. Let P(u, v) be a shortest path between u and v."

**Formalization Note.**
* **Edge list.** A graph is an edge list on the vertex set `Fin n`: edge `e : Fin m` joins `src e` and
  `dst e` and has weight `wt e`. Parallel edges and loops are allowed, which is more general than the
  page's `G = (V, E)`; a loop never shortens a walk and a parallel edge only adds walks.
* **Oriented edges.** An oriented edge is a pair `(e, o)`: `o = false` is the orientation
  `(src e, dst e)`, `o = true` the orientation `(dst e, src e)`.
* **Walks.** A walk from `u` to `v` is a list of oriented edges, each starting where the previous one
  ends. With positive weights a shortest walk repeats no vertex, so shortest walks are the page's
  shortest paths.
* **Distance.** `dist G u v` is the infimum of the lengths of the walks from `u` to `v`. Under the
  standing assumptions (`PosWeights`, `Connected`) the set of lengths is nonempty and bounded below by
  `0`, and the infimum is attained, so `dist` is the page's `d(u, v)`. The junk value `sInf ∅ = 0` only
  occurs for disconnected graphs, which every statement excludes.
* **Connected** includes `0 < n`: a connected graph has a vertex.
-/

/-- §2, p.6: an undirected (multi)graph on `Fin n` given as an edge list with real weights. -/
structure Graph where
  /-- the number of vertices -/
  n : ℕ
  /-- the number of edges -/
  m : ℕ
  /-- one endpoint of each edge -/
  src : Fin m → Fin n
  /-- the other endpoint of each edge -/
  dst : Fin m → Fin n
  /-- the weight `ℓ` of each edge -/
  wt : Fin m → ℝ

/-- §2, p.6: positive real edge weights. -/
def Graph.PosWeights (G : Graph) : Prop := ∀ e, 0 < G.wt e

/-- The tail of an oriented edge `(e, o)`: `src e` for `o = false`, `dst e` for `o = true`. -/
def Graph.tail (G : Graph) (s : Fin G.m × Bool) : Fin G.n :=
  if s.2 then G.dst s.1 else G.src s.1

/-- The head of an oriented edge `(e, o)`: `dst e` for `o = false`, `src e` for `o = true`. -/
def Graph.head (G : Graph) (s : Fin G.m × Bool) : Fin G.n :=
  if s.2 then G.src s.1 else G.dst s.1

/-- `IsWalk G u v W`: the list `W` of oriented edges is a walk from `u` to `v`. -/
def IsWalk (G : Graph) : Fin G.n → Fin G.n → List (Fin G.m × Bool) → Prop
  | u, v, [] => u = v
  | u, v, s :: W => G.tail s = u ∧ IsWalk G (G.head s) v W

/-- The length of a walk: the sum of the weights of its edges. -/
def walkLen (G : Graph) (W : List (Fin G.m × Bool)) : ℝ :=
  (W.map fun s => G.wt s.1).sum

/-- §2, p.6: `G` is connected (and has a vertex): every two vertices are joined by a walk. -/
def Graph.Connected (G : Graph) : Prop :=
  0 < G.n ∧ ∀ u v : Fin G.n, ∃ W, IsWalk G u v W

/-- §2, p.6: the distance `d(u, v)`, the least length of a walk from `u` to `v`. -/
noncomputable def dist (G : Graph) (u v : Fin G.n) : ℝ :=
  sInf {c : ℝ | ∃ W, IsWalk G u v W ∧ walkLen G W = c}

/-- §2, p.7: `W` is a shortest path `P(u, v)`: a walk from `u` to `v` of length `d(u, v)`. -/
def IsShortestWalk (G : Graph) (u v : Fin G.n) (W : List (Fin G.m × Bool)) : Prop :=
  IsWalk G u v W ∧ walkLen G W = dist G u v

end TZLevelsADO


