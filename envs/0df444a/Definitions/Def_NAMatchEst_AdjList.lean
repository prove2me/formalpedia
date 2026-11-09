-- Prove2me | Definitions.Def_NAMatchEst_AdjList
-- name    : NAMatchEst_AdjList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:13.758874+00:00
-- url     : https://prove2.me/theorems/085df1c0-3bdb-47df-a89a-baf4af767590
-- title:
--   Adjacency-list representation of a simple graph on $n$ vertices
-- statement:
--   An **adjacency-list representation** of a simple undirected graph on the vertex set $V=\{0,\dots,n-1\}$ assigns to every vertex $v$ a finite list $\mathrm{adj}(v)$ of vertices, in a fixed order, such that
--
--   1. no vertex occurs twice in a list;
--   2. no vertex occurs in its own list;
--   3. $u$ occurs in the list of $v$ exactly when $v$ occurs in the list of $u$.
--
--   The list of $v$ is its neighbourhood $N(v)$, written in the order in which the oracle reports it. The order is part of the data: quantifying over all adjacency-list representations quantifies over every simple graph on $n$ vertices together with every ordering of its adjacency lists, which is the generality of the paper's guarantees ("the guarantee holds for every ordering of the adjacency lists").
--
--   **Formalization Note** Vertices are `Fin n`; the lists are `List (Fin n)`.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17) and §3.2, p.19 (PDF 23)

import Mathlib

namespace NAMatchEst

/-- An **adjacency-list representation** of a simple undirected graph on the vertex set
`Fin n`: every vertex `v` carries a list `adj v` of its neighbours, in a fixed order.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17) ("We have query access to the adjacency list") and §3.2, p.19
(PDF 23) ("Fix a simple undirected graph G = (V, E) with |V| = n. … The ordering of each
adjacency list is arbitrary and fixed.").

**Formalization Note** The lists have no repeated entries (`nodup`), no vertex lists itself
(`loopless`), and `u` is in the list of `v` exactly when `v` is in the list of `u` (`symm`), so
the lists are the neighbourhoods of a simple undirected graph (`AdjList.toGraph`). The order of
each list is part of the data: quantifying over all `AdjList n` is quantifying over every simple
graph on `n` vertices together with every ordering of its adjacency lists. -/
structure AdjList (n : ℕ) where
  /-- The adjacency list of `v`, in its fixed order. -/
  adj : Fin n → List (Fin n)
  /-- No neighbour is listed twice. -/
  nodup : ∀ v, (adj v).Nodup
  /-- No vertex is its own neighbour. -/
  loopless : ∀ v, v ∉ adj v
  /-- The neighbour relation is symmetric. -/
  symm : ∀ u v, u ∈ adj v ↔ v ∈ adj u

end NAMatchEst


