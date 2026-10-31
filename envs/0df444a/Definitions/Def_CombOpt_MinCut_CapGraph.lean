-- Prove2me | Definitions.Def_CombOpt_MinCut_CapGraph
-- name    : CombOpt_MinCut_CapGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:20.410506+00:00
-- url     : https://prove2.me/theorems/f31eab99-4a58-4010-a56d-ebd08b2018ab
-- title:
--   Finite capacitated multigraph $G=(V,E)$ with capacities $u\in\mathbb R^E$
-- statement:
--   A **capacitated graph** $G=(V,E)$ consists of a set $V$ of nodes, a set $E$ of edges, for each edge $e$ the unordered pair of its ends, and a capacity $u_e\in\mathbb R$ for each edge.
--
--   Graphs are multigraphs in the sense of the book: two edges may have the same ends (parallel edges), and an edge may have both ends equal (a loop). Node identification, the operation at the heart of the minimum cut algorithms of §3.5, creates parallel edges, so they cannot be excluded.
--
--   This is the object on which every cut, minimum cut value and legal ordering of the mission is defined.
--
--   **Formalization Note** The nodes and edges are Lean types `V` and `E` (finite where a statement requires it) and `ends : E → Sym2 V`. The capacity is an arbitrary real function; the sign condition of the book ($u_e>0$, p. 72) is a hypothesis of the theorems that use it.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 9 (PDF p. 18) (graphs); §3.5, p. 72 (PDF p. 81) (capacity function u ∈ R^E)

import Mathlib

namespace CombOpt.MinCut

/-- **A finite capacitated (multi)graph `G = (V, E)` with capacities `u ∈ ℝ^E`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 9
(PDF p. 18): "An (undirected) graph G consists of disjoint finite sets V(G) of nodes, and E(G) of
edges, and a relation associating with each edge a pair of nodes, its ends. … Two edges having the
same ends are said to be parallel; an edge whose ends are the same is called a loop"; §3.5, p. 72
(PDF p. 81): "a graph G = (V, E) and a capacity function u ∈ ℝ^E".

The node set is the type `V`, the edge set the type `E` (finite through `[Fintype V]`,
`[Fintype E]` where a statement needs it), `ends e` is the unordered pair of ends of the edge `e`,
and `u e` is its capacity.

**Formalization Note.** Parallel edges are distinct elements of `E` with the same `ends`; a loop
is an edge whose `ends` is a diagonal pair `s(a, a)`. Both are allowed, as in the book (node
identification creates parallel edges, p. 73): this is not a `SimpleGraph`. The capacity is an
arbitrary real function; the sign condition the book imposes (`u_e > 0`, p. 72) is a hypothesis of
the theorems that need one. -/
structure CapGraph (V E : Type*) where
  /-- The unordered pair of ends of each edge. -/
  ends : E → Sym2 V
  /-- The capacity `u_e` of each edge. -/
  u : E → ℝ

end CombOpt.MinCut


