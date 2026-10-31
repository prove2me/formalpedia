-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_Graph
-- name    : CombOpt_MatroidPolytope_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:55.764025+00:00
-- url     : https://prove2.me/theorems/b7107232-abe6-4b28-9818-748604fab2c9
-- title:
--   Finite graph with loops and parallel edges
-- statement:
--   A **graph** $G=(V,E)$ consists of a finite set $V$ of nodes, a finite set $E$ of edges, and, for every edge, the unordered pair of its **ends**. Parallel edges (same ends) and loops (both ends equal) are allowed.
--
--   **Formalization Note** Nodes and edges are types `V` and `E`; `ends : E → Sym2 V`. This is not Mathlib's `SimpleGraph`. The same structure is drafted in other chapters of this series under their own sub-namespaces; drafts cannot import each other.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 9 (PDF p. 18)

import Mathlib

namespace CombOpt.MatroidPolytope

/-- **A finite (multi)graph.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 9 (PDF p. 18): "An (undirected) graph G consists of disjoint finite sets V(G) of
nodes, and E(G) of edges, and a relation associating with each edge a pair of nodes, its ends.
… Two edges having the same ends are said to be parallel; an edge whose ends are the same is
called a loop".

The node set is the type `V`, the edge set the type `E` (finite where a statement needs it),
and `ends e` is the unordered pair of ends of the edge `e`.

**Formalization Note.** Parallel edges and loops (`ends e = s(v, v)`) are allowed; this is not
Mathlib's `SimpleGraph`. -/
structure Graph (V E : Type*) where
  /-- The unordered pair of ends of each edge. -/
  ends : E → Sym2 V

end CombOpt.MatroidPolytope


