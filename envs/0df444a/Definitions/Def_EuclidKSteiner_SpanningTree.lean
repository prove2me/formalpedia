-- Prove2me | Definitions.Def_EuclidKSteiner_SpanningTree
-- name    : EuclidKSteiner_SpanningTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:04.01532+00:00
-- url     : https://prove2.me/theorems/43992ddf-b02d-4817-8f05-b1ad82a48b47
-- title:
--   Spanning trees, minimum spanning trees and MST weight of a finite weighted multigraph
-- statement:
--   Let $V$ be a type of vertices, $\iota$ a type of edge names, $\mathrm{ends}:\iota\to\mathrm{Sym}^2(V)$ the endpoint map and $E_s$ a finite set of edges; this is a finite multigraph (parallel edges and loops allowed). Simple graphs are the case $\iota=\mathrm{Sym}^2(V)$, $\mathrm{ends}=\mathrm{id}$.
--
--   1. A set $T\subseteq E_s$ is a **spanning tree** of a finite vertex set $X$ if no edge of $T$ is a loop, all endpoints of edges of $T$ lie in $X$, any two vertices of $X$ are joined by a walk using edges of $T$, and $|T|=|X|-1$. (Connectivity and the edge count make $T$ acyclic.)
--   2. For edge weights $w$, the weight of an edge set is $w(H)=\sum_{e\in H}w(e)$, and $T$ is a **minimum spanning tree** if it is a spanning tree with $w(T)\le w(T')$ for every spanning tree $T'$.
--   3. The **MST weight** $w(\mathrm{MST}(X))$ is the minimum of $w(T)$ over the finite set of spanning trees, a minimum attained by a tree; it is $0$ when no spanning tree exists (empty or disconnected $X$). For $|X|=1$ the only spanning tree is $\emptyset$.
--   4. $\mathrm{cc}(H)$ is the number of connected components of the graph on all of $V$ with edge set $H$, and $H_{\le t}$ is the set of edges of weight at most $t$.
--
--   These are the graph-theoretic primitives of the whole mission: the Euclidean MST of the problem statement, the attachment value $\Phi$, the threshold formula and the completion formula.
--
--   **Formalization Note** The complete graph on $X$ has edge set all unordered pairs of distinct elements of $X$ (`completeEdges`).
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), §1 p.1 (PDF p.3); §3 pp.8–10 (PDF pp.10–12)

import Mathlib

namespace EuclidKSteiner

open Classical

/-!
# Spanning trees and minimum spanning tree weight of a finite weighted (multi)graph

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), §1 p.1 (PDF p.3) and §3 pp.8–10 (PDF pp.10–12):
"w(G) = ∑_{uv∈E(G)} ∥u−v∥₂", "MST(X) denote a Euclidean minimum spanning tree", "For a graph or an
edge set H, write w(H) for its total edge weight", "For a graph H, write cc(H) for its number of
connected components".

**Formalization Note** A finite multigraph is given by an index type `ι` of edges, a map
`ends : ι → Sym2 V` giving the two endpoints of each edge, and a finite edge set `Es : Finset ι`;
simple graphs are the case `ι = Sym2 V`, `ends = id`. Loops are never tree edges. The weight of an
edge set is a plain finite sum. The minimum spanning tree weight is a genuine minimum over the
finite, nonempty set of spanning trees; it is `0` only when there is no spanning tree at all
(an empty or disconnected vertex set), a case every statement of the mission excludes or in which
the paper's own convention is `0` (`|X| ≤ 1`).
-/

/-- `T` is a **spanning tree** of the vertex set `X` in the multigraph `(ends, Es)`: its edges are
edges of the graph, no edge is a loop, all endpoints lie in `X`, any two vertices of `X` are joined
by a walk of `T`, and `T` has exactly `|X| − 1` edges (written `|T| + 1 = |X|`, so `X ≠ ∅`).
Connectivity together with the edge count makes `T` acyclic, hence a tree; two parallel edges are
excluded because the simple graph of `T` would then have too few edges to connect `X`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, STOC 2027 submission (manuscript sha256 75361687…),
§1 p.1 (PDF p.3) and §3 p.8 (PDF p.10). -/
def IsSpanningTree {V ι : Type*} (X : Finset V) (ends : ι → Sym2 V) (Es T : Finset ι) : Prop :=
  T ⊆ Es ∧ (∀ i ∈ T, ¬ (ends i).IsDiag ∧ ∀ v ∈ ends i, v ∈ X) ∧
    (∀ u ∈ X, ∀ v ∈ X,
      (SimpleGraph.fromEdgeSet (ends '' (T : Set ι))).Reachable u v) ∧
    T.card + 1 = X.card

/-- The total weight `w(H) = ∑_{e ∈ H} w(e)` of a finite edge set.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §3, p.8 (PDF p.10). -/
def edgeSum {ι : Type*} (wt : ι → ℝ) (T : Finset ι) : ℝ :=
  ∑ i ∈ T, wt i

/-- `T` is a **minimum spanning tree** of `X` in `(ends, Es)` for the weights `wt`: a spanning tree
whose weight is at most that of every spanning tree.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §1 p.1 (PDF p.3). -/
def IsMST {V ι : Type*} (X : Finset V) (ends : ι → Sym2 V) (Es : Finset ι) (wt : ι → ℝ)
    (T : Finset ι) : Prop :=
  IsSpanningTree X ends Es T ∧
    ∀ T' : Finset ι, IsSpanningTree X ends Es T' → edgeSum wt T ≤ edgeSum wt T'

/-- The finite set of spanning trees of `X` in `(ends, Es)`. -/
noncomputable def spanningTrees {V ι : Type*} (X : Finset V) (ends : ι → Sym2 V)
    (Es : Finset ι) : Finset (Finset ι) :=
  Es.powerset.filter (fun T => IsSpanningTree X ends Es T)

/-- **Minimum spanning tree weight** `w(MST(H))`: the least weight of a spanning tree of `X` in
`(ends, Es)`, a minimum over a finite set, attained by a tree. It is `0` when `X` has no spanning
tree (empty or disconnected `X`). For `|X| = 1` the only spanning tree is `∅`, of weight `0`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §1 p.1 (PDF p.3), §3 (3.1)–(3.2), pp.10 (PDF p.12). -/
noncomputable def mstWeightOn {V ι : Type*} (X : Finset V) (ends : ι → Sym2 V) (Es : Finset ι)
    (wt : ι → ℝ) : ℝ :=
  if h : (spanningTrees X ends Es).Nonempty then
    (spanningTrees X ends Es).inf' h (edgeSum wt)
  else 0

/-- The edges of the **complete graph** on a finite vertex set `X`: all unordered pairs of distinct
elements of `X`. -/
def completeEdges {V : Type*} [DecidableEq V] (X : Finset V) : Finset (Sym2 V) :=
  X.sym2.filter (fun e => ¬ e.IsDiag)

/-- The **number of connected components** `cc(H)` of the multigraph on all of `V` with the edge
set `T` (vertices with no edge are components of their own).
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §3.2, p.9 (PDF p.11): "For a graph H, write cc(H) for
its number of connected components." -/
noncomputable def numComponents {V ι : Type*} (ends : ι → Sym2 V) (T : Finset ι) : ℕ :=
  Nat.card (SimpleGraph.fromEdgeSet (ends '' (T : Set ι))).ConnectedComponent

/-- The **threshold subgraph** `H_{≤t}`: the edges of `Es` of weight at most `t` (on all vertices).
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §3.2, p.10 (PDF p.12): "let H≤t be the spanning subgraph
with all vertices of H and exactly its edges of weight at most t". -/
noncomputable def thresholdEdges {ι : Type*} (Es : Finset ι) (wt : ι → ℝ) (t : ℝ) : Finset ι :=
  Es.filter (fun i => wt i ≤ t)

end EuclidKSteiner


