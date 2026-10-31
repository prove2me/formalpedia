-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph
-- name    : CombOpt_HeldKarp_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:52.792815+00:00
-- url     : https://prove2.me/theorems/853f57c6-3023-45f6-9b68-31fe002441fd
-- title:
--   Finite graph with loops and parallel edges
-- statement:
--   A **graph** $G=(V,E)$ consists of a finite set $V$ of **nodes**, a finite set $E$ of **edges**, and, for every edge $e$, the unordered pair of its **ends**. Two edges with the same ends are **parallel**; an edge whose two ends coincide is a **loop**. Both are allowed.
--
--   This is the graph model of the whole book; every object of this mission is defined on such a graph.
--
--   **Formalization Note** Nodes and edges are types `V` and `E` (finite where needed), and `ends : E → Sym2 V` gives the unordered pair of ends. This is not Mathlib's `SimpleGraph`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 9 (PDF p. 18)

import Mathlib

namespace CombOpt.HeldKarp

/-- **A finite (multi)graph.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 9
(PDF p. 18): "An (undirected) graph G consists of disjoint finite sets V(G) of nodes, and E(G) of
edges, and a relation associating with each edge a pair of nodes, its ends. … Two edges having the
same ends are said to be parallel; an edge whose ends are the same is called a loop".

The node set is the type `V`, the edge set the type `E` (finite where a statement needs it, through
`[Fintype V]`, `[Fintype E]`), and `ends e` is the unordered pair of ends of the edge `e`.

**Formalization Note.** Parallel edges are distinct elements of `E` with the same `ends`; a loop is
an edge whose `ends` is a diagonal pair `s(v, v)`. Both are allowed, as in the book: this is not a
`SimpleGraph`. -/
structure Graph (V E : Type*) where
  /-- The unordered pair of ends of each edge. -/
  ends : E → Sym2 V

end CombOpt.HeldKarp


