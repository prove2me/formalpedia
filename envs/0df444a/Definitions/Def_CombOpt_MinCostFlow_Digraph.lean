-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph
-- name    : CombOpt_MinCostFlow_Digraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:20.359316+00:00
-- url     : https://prove2.me/theorems/fb4068bb-5f7b-402f-9808-279a19607764
-- title:
--   Digraph (directed multigraph)
-- statement:
--   A **digraph** $G$ consists of finite sets $V$ of *nodes* and $E$ of *arcs*, together with functions assigning to each arc $e\in E$ a *tail* $t(e)\in V$ and a *head* $h(e)\in V$. Loops ($t(e)=h(e)$) and parallel arcs are allowed.
--
--   This is the network on which the minimum-cost flow problem (4.1) and the feasibility theorem 3.18 are posed.
--
--   **Formalization Note** Nodes and arcs are the types `V` and `E`; finiteness is supplied by `Fintype` instances where a statement needs it.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 19 (PDF p. 28)

import Mathlib

namespace CombOpt.MinCostFlow

/-- **A digraph (directed multigraph).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 19 (PDF p. 28): "A *directed graph* or *digraph* G consists of disjoint finite
sets V = V(G) of *nodes* and E = E(G) of *arcs*, and functions associating to each e ∈ E a
*tail* t(e) ∈ V and a *head* h(e) ∈ V." This is the network of the minimum-cost flow problem
(4.1), §4.1, p. 91 (PDF p. 99).

**Formalization Note.** The node set is the type `V` and the arc set the type `E` (finite where a
statement needs it, through `[Fintype V]`, `[Fintype E]`). Loops (`tail e = head e`) and parallel
arcs are allowed, as in the book. -/
structure Digraph (V E : Type*) where
  /-- The tail `t(e)` of each arc. -/
  tail : E → V
  /-- The head `h(e)` of each arc. -/
  head : E → V

end CombOpt.MinCostFlow


