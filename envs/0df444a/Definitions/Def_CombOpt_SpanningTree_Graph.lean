-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph
-- name    : CombOpt_SpanningTree_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:20.848288+00:00
-- url     : https://prove2.me/theorems/16d65806-0943-428c-90ff-eef4b91a8393
-- title:
--   Finite graph with loops and parallel edges
-- statement:
--   A **graph** $G=(V,E)$ consists of a finite set $V$ of **nodes**, a finite set $E$ of **edges**, and, for every edge $e$, the unordered pair of its **ends**. Two edges with the same ends are **parallel**; an edge whose two ends coincide is a **loop**. Both are allowed.
--
--   This is the graph model of the whole book: every statement of this mission is about such a graph.
--
--   **Formalization Note** The node set and edge set are types `V` and `E` (finite where a statement needs it), and `ends : E → Sym2 V` gives the unordered pair of ends. Parallel edges are distinct elements of `E` with equal `ends`; a loop has `ends e = s(v, v)`. This is not Mathlib's `SimpleGraph`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 9 (PDF p. 18)

import Mathlib

namespace CombOpt.SpanningTree

/-- **A finite (multi)graph.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 9 (PDF p. 18): "An (undirected) graph G consists of disjoint finite sets V(G) of
nodes, and E(G) of edges, and a relation associating with each edge a pair of nodes, its ends.
… Two edges having the same ends are said to be parallel; an edge whose ends are the same is
called a loop".

The node set is the type `V`, the edge set the type `E` (both finite where a statement needs it,
through `[Fintype V]`, `[Fintype E]`), and `ends e` is the unordered pair of ends of the edge `e`.

**Formalization Note.** Parallel edges are distinct elements of `E` with the same `ends`; a loop
is an edge whose `ends` is a diagonal pair `s(v, v)`. Both are allowed, as in the book: this is
not a `SimpleGraph`. Disjointness of `V(G)` and `E(G)` is automatic for two types. -/
structure Graph (V E : Type*) where
  /-- The unordered pair of ends of each edge. -/
  ends : E → Sym2 V

end CombOpt.SpanningTree


