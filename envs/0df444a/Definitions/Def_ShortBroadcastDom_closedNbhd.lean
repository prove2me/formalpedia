-- Prove2me | Definitions.Def_ShortBroadcastDom_closedNbhd
-- name    : ShortBroadcastDom_closedNbhd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:23.238079+00:00
-- url     : https://prove2.me/theorems/6027d36f-fb50-4105-a969-b89bb35a2062
-- title:
--   Closed neighbourhood $N_G[v]$ and domination of a demand set $R\subseteq N_G[D]$
-- statement:
--   All graphs are finite, simple and undirected. For a vertex $v$ of a graph $G$, the **open neighbourhood** $N_G(v)$ is the set of neighbours of $v$, and the **closed neighbourhood** is
--
--   $$
--   N_G[v]=N_G(v)\cup\{v\}.
--   $$
--
--   For a set $X$ of vertices, $N_G[X]=\bigcup_{v\in X}N_G[v]$. A set $D$ **dominates** a demand set $R$ if
--
--   $$
--   R\subseteq N_G[D],
--   $$
--
--   that is, every demand is in $D$ or adjacent to a vertex of $D$; the dominating vertices ("candidates") may lie anywhere in the graph. A **dominating set** of $G$ is a set dominating $R=V(G)$.
--
--   These are the basic objects of every covering statement in the mission.
--
--   **Formalization Note** The vertex type is a `Fintype`; $N_G[v]$ is `insert v (G.neighborFinset v)`.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §4, p.14 (PDF p.17)

import Mathlib

namespace ShortBroadcastDom

/-- The closed neighbourhood `N_G[v] = N_G(v) ∪ {v}` of a vertex `v` of a finite simple graph.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §4, p.14 (PDF 17): "All graphs are finite, simple, and undirected. Write N_G(v) and
N_G[v] for open and closed neighborhoods".

**Formalization Note** Graphs are `SimpleGraph V` on a `Fintype V`; `N_G(v)` is Mathlib's
`G.neighborFinset v` and `N_G[v] = insert v (G.neighborFinset v)`. -/
def closedNbhd {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Finset V :=
  insert v (G.neighborFinset v)

/-- `DominatesSet G R D`: the vertex set `D` dominates the demand set `R`, i.e. `R ⊆ N_G[D]`;
every demand lies in the closed neighbourhood of some vertex of `D`.

§4, p.14 (PDF 17): "A set D dominates a demand set R if R ⊆ N[D], and candidates may lie
anywhere in the graph." A dominating set of `G` is a set dominating `R = V(G)`.

**Formalization Note** `N[D] = ⋃_{v ∈ D} N[v]`, so `r ∈ N[D]` is `∃ v ∈ D, r ∈ N[v]`. -/
def DominatesSet {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R D : Finset V) : Prop :=
  ∀ r ∈ R, ∃ v ∈ D, r ∈ closedNbhd G v

end ShortBroadcastDom


