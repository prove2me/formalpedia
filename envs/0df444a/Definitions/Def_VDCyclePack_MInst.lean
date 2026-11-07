-- Prove2me | Definitions.Def_VDCyclePack_MInst
-- name    : VDCyclePack_MInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:33.782057+00:00
-- url     : https://prove2.me/theorems/071288c3-e7cc-4784-bfbc-1de1fdf13b93
-- title:
--   An encoded auxiliary multigraph
-- statement:
--   An encoded multigraph is a number $n$ of vertices and a list of edges, each a pair of vertices in $\{0,\dots,n-1\}$; a pair with equal entries is a loop and repeated pairs are parallel edges. It is the input of the algorithm of Lemma 6.2.
--
--   **Formalization Note** Edges are indexed by their position in the list.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 6.2, p.18, and Section 3, p.10

import Mathlib

namespace VDCyclePack

/-- **An encoded auxiliary multigraph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 6.2, p.18 ("such cycles can be found in polynomial time"), Section 3, p.10
("Auxiliary multigraphs may have loops and parallel edges").

An `MInst` is a number of vertices `n` and a list of edges, each an (unordered) pair of vertices of
`Fin n`; equal pairs are loops and repeated pairs are parallel edges.

**Formalization Note.** Edges are indexed by their position in the list. -/
structure MInst where
  /-- number of vertices -/
  n : ℕ
  /-- edges, as pairs of vertices; position in the list is the edge index -/
  edges : List (Fin n × Fin n)

end VDCyclePack


