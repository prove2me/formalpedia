-- Prove2me | Definitions.Def_VDCyclePack_GraphInst
-- name    : VDCyclePack_GraphInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:36.329278+00:00
-- url     : https://prove2.me/theorems/900086f1-63c1-4e9e-a6ab-2675f542b564
-- title:
--   An encoded input graph
-- statement:
--   An encoded graph is a number $n$ of vertices together with a list of pairs of vertex indices.
--
--   It is the input of the algorithms of Theorem 1.1, Lemma 4.1, Theorem 4.2, Lemma 4.3, Lemma 3.1 and Proposition 6.3.
--
--   **Formalization Note** Vertices are $0,\dots,n-1$. Loops, repeated pairs, both orientations and out-of-range indices are allowed and ignored by the graph map, so every finite simple graph on $n$ labelled vertices is the graph of some instance.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 1.1, p.3

import Mathlib

namespace VDCyclePack

/-- **An encoded input graph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 1.1, p.3: "given a finite simple undirected graph G".

A `GraphInst` is a number of vertices `n` and a list of edges, each a pair of vertex indices.

**Formalization Note.** Vertices are `0, …, n − 1`. Loops, repeated edges, both orientations and
out-of-range entries are allowed in the list and are ignored by `GraphInst.toGraph`, so every
finite simple graph on `n` labelled vertices is the graph of some instance and no
well-formedness condition is needed. -/
structure GraphInst where
  /-- number of vertices -/
  n : ℕ
  /-- edges as pairs of vertex indices -/
  edges : List (ℕ × ℕ)

end VDCyclePack


