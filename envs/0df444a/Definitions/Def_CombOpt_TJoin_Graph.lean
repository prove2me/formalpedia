-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph
-- name    : CombOpt_TJoin_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:03:41.640348+00:00
-- url     : https://prove2.me/theorems/b7a15f9d-75d3-4efb-a910-04c7e631df3a
-- title:
--   Finite graph with loops and parallel edges
-- statement:
--   A **graph** $G=(V,E)$ consists of a finite set $V$ of nodes, a finite set $E$ of edges, and for each edge $e$ the unordered pair of its **ends** (two nodes, possibly equal). Two edges with the same ends are **parallel**; an edge whose two ends coincide is a **loop**. Both are allowed.
--
--   Every statement of this mission is about such a graph; it is a multigraph, not a simple graph.
--
--   **Formalization Note** The node and edge sets are types `V` and `E` (finite where needed via `Fintype`), and `ends e : Sym2 V` is the unordered pair of ends; a loop has a diagonal pair.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 9 (PDF p. 18)

import Mathlib

namespace CombOpt.TJoin

/-- **A finite (multi)graph.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 9 (PDF p. 18): "An (undirected) graph G consists of disjoint finite sets V(G)
of nodes, and E(G) of edges, and a relation associating with each edge a pair of nodes, its ends.
… Two edges having the same ends are said to be parallel; an edge whose ends are the same is
called a loop".

The node set is the type `V`, the edge set the type `E` (finite through `[Fintype V]`,
`[Fintype E]` wherever a statement needs it), and `ends e` is the unordered pair of ends of `e`.

**Formalization Note.** Parallel edges are distinct elements of `E` with the same `ends`; a loop
is an edge whose `ends` is a diagonal pair `s(v, v)`. Both are allowed, as in the book: this is
not a `SimpleGraph`. -/
structure Graph (V E : Type*) where
  /-- The unordered pair of ends of each edge. -/
  ends : E → Sym2 V

end CombOpt.TJoin


