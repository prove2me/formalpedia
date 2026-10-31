-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_Graph
-- name    : CombOpt_MatchingPolytope_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:19.311295+00:00
-- url     : https://prove2.me/theorems/eea6aea5-4fd0-4d66-aae4-280ceb6800eb
-- title:
--   A finite multigraph $G=(V,E)$ with loops and parallel edges
-- statement:
--   A **graph** $G=(V,E)$ consists of a finite set $V$ of **nodes**, a finite set $E$ of **edges**, and a relation associating with each edge an unordered pair of nodes, its **ends**. Two edges with the same ends are **parallel**; an edge whose two ends coincide is a **loop**. Both are allowed.
--
--   This is the graph notion of the whole book, and every graph statement of this mission is about such a $G$.
--
--   **Formalization Note** The nodes form a type $V$ and the edges a type $E$; `ends e` is an unordered pair `Sym2 V`. Parallel edges are distinct elements of $E$ with equal ends, so this is not Mathlib's `SimpleGraph`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 9 (PDF p. 18)

import Mathlib

namespace CombOpt.MatchingPolytope

/-- **A finite (multi)graph.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 9 (PDF p. 18): "An (undirected) graph G consists of disjoint finite sets V(G) of
nodes, and E(G) of edges, and a relation associating with each edge a pair of nodes, its ends.
… Two edges having the same ends are said to be parallel; an edge whose ends are the same is
called a loop".

The node set is the type `V`, the edge set the type `E` (finite where a statement needs it,
through `[Fintype V]`, `[Fintype E]`), and `ends e` is the unordered pair of ends of `e`.

**Formalization Note.** Parallel edges are distinct elements of `E` with the same `ends`; a loop
is an edge whose `ends` is a diagonal pair `s(v, v)`. Both are allowed, as in the book: this is
not a `SimpleGraph`. -/
structure Graph (V E : Type*) where
  /-- The unordered pair of ends of each edge. -/
  ends : E → Sym2 V

end CombOpt.MatchingPolytope


