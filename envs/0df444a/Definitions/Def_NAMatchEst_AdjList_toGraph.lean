-- Prove2me | Definitions.Def_NAMatchEst_AdjList_toGraph
-- name    : NAMatchEst_AdjList_toGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:50:01.937257+00:00
-- url     : https://prove2.me/theorems/94ca27bf-47d9-444b-934e-f2598bad1d2d
-- title:
--   The simple graph of an adjacency-list representation
-- statement:
--   The simple graph $G=(V,E)$ described by an adjacency-list representation: $u$ and $v$ are adjacent exactly when $v$ occurs in the list of $u$. By the symmetry and looplessness of the lists this is a simple undirected graph, and the degree $\deg(v)=|N(v)|$ is the length of the list of $v$.
--
--   Every statement of the mission about $\mu(G)$, $E(G[S])$ or matchings refers to this graph.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2, p.13 (PDF 17) and §3.2, p.19 (PDF 23)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList

namespace NAMatchEst

/-- The simple graph `G = (V, E)` described by an adjacency-list representation: `u` and `v` are
adjacent iff `v` occurs in the adjacency list of `u`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2, p.13 (PDF 17) (N(v), deg(v) = |N(v)|) and §3.2, p.19 (PDF 23).

**Formalization Note** By `AdjList.symm` and `AdjList.loopless` this relation is symmetric and
irreflexive. The degree of `v` is the length of its list (the list has no duplicates). -/
def AdjList.toGraph {n : ℕ} (G : AdjList n) : SimpleGraph (Fin n) where
  Adj u v := v ∈ G.adj u
  symm := ⟨fun u v h => (G.symm u v).2 h⟩
  loopless := ⟨fun v h => G.loopless v h⟩

instance AdjList.instDecidableRelToGraph {n : ℕ} (G : AdjList n) :
    DecidableRel G.toGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (v ∈ G.adj u))

end NAMatchEst


