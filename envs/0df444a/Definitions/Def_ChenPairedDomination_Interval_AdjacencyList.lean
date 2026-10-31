-- Prove2me | Definitions.Def_ChenPairedDomination_Interval_AdjacencyList
-- name    : ChenPairedDomination_Interval_AdjacencyList
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T01:25:26.973601+00:00
-- url     : https://prove2.me/theorems/59deafae-a6aa-4b1c-8bd3-09cb5e9dee75
-- title:
--   Duplicate-free indexed adjacency lists and the undirected edge count
-- statement:
--   An adjacency-list representation of a simple graph on Fin n has an array of n rows. Each row is a duplicate-free list of natural indices less than n, and membership in row i agrees exactly with graph adjacency from i. Row orders are arbitrary. The edge count counts adjacent pairs i < j once. This representation certifies only the input graph: it assumes no algorithmic correctness, no earlier-neighbor existence, and no bound on how often an edge is visited.
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, §3, Algorithm MPDI and Theorem 10, pp. 12–13; explicit unit-cost graph-input convention

import Mathlib.Combinatorics.SimpleGraph.Finite

namespace ChenPairedDomination.Interval

/-- An indexed, duplicate-free adjacency-list representation; no algorithmic promises. -/
structure AdjacencyList (n : ℕ) (G : SimpleGraph (Fin n)) where
  rows : Array (List ℕ)
  size_eq : rows.size = n
  bounded : ∀ i : Fin n, ∀ j ∈ rows[i.val]!, j < n
  nodup : ∀ i : Fin n, (rows[i.val]!).Nodup
  represents : ∀ i j : Fin n, j.val ∈ rows[i.val]! ↔ G.Adj i j

/-- Each undirected edge is counted once, by its smaller endpoint. -/
noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

end ChenPairedDomination.Interval


