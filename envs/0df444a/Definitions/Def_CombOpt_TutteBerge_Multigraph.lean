-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph
-- name    : CombOpt_TutteBerge_Multigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:03:26.432627+00:00
-- url     : https://prove2.me/theorems/f826d730-7f01-422a-86be-2bbb467004c0
-- title:
--   Graph (finite multigraph with loops and parallel edges)
-- statement:
--   A **graph** $G=(V,E)$ consists of a set $V$ of nodes, a set $E$ of edges, and, for each edge $e$, the unordered pair of its **ends**. The two ends may coincide (a **loop**), and distinct edges may have the same ends (**parallel** edges).
--
--   This is the graph model of the book. It is needed in this mission because shrinking an odd circuit produces parallel edges, and because the edges of the shrunk graph must remain edges of the original graph.
--
--   **Formalization Note** The nodes and edges are the types `V` and `E`; `ends e : Sym2 V` is the unordered pair of ends. Finiteness is not bundled: every theorem assumes `[Finite V] [Finite E]`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 9 (PDF p. 18)

import Mathlib

namespace CombOpt.TutteBerge

/-- **A graph (finite multigraph).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 9 (PDF p. 18): "An (undirected) *graph* G consists of disjoint finite sets V(G) of
*nodes*, and E(G) of *edges*, and a relation associating with each edge a pair of nodes, its
*ends*."

The node set is the type `V`, the edge set the type `E`; `ends e` is the unordered pair of ends of
`e`.

**Formalization Note.** Loops (`ends e` a diagonal `s(v, v)`) and parallel edges (`e ≠ f` with
`ends e = ends f`) are allowed, as in the book (p. 9). Finiteness is not part of the structure:
every theorem of this development takes `[Finite V] [Finite E]`. Disjointness of `V` and `E` is
automatic for two types. -/
structure Multigraph (V E : Type*) where
  /-- The unordered pair of ends of each edge. -/
  ends : E → Sym2 V

end CombOpt.TutteBerge


