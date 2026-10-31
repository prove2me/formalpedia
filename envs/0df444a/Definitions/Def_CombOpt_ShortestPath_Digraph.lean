-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph
-- name    : CombOpt_ShortestPath_Digraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:22.556643+00:00
-- url     : https://prove2.me/theorems/e7a6cec3-6278-4833-8fff-27a17089ee94
-- title:
--   Digraph (finite directed multigraph with tails and heads)
-- statement:
--   A **digraph** $G$ consists of disjoint finite sets $V=V(G)$ of **nodes** and $E=E(G)$ of **arcs**, together with functions assigning to each arc $e\in E$ a **tail** $t(e)\in V$ and a **head** $h(e)\in V$. We write $e=vw$ when $t(e)=v$ and $h(e)=w$.
--
--   Loops ($t(e)=h(e)$) and parallel arcs (distinct arcs with the same tail and head) are allowed; a digraph without them is called simple. This is the object on which every shortest path statement of the chapter is made.
--
--   **Formalization Note** The node and arc sets are types `V` and `E`; finiteness is imposed by `[Fintype V] [Fintype E]` in each statement. This is not Mathlib's `Digraph` (an adjacency relation, which cannot carry parallel arcs).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 19 (PDF p. 28), definition of a directed graph

import Mathlib

namespace CombOpt.ShortestPath

/-- **A digraph (directed multigraph).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 19 (PDF p. 28): "A *directed graph* or *digraph* G consists of disjoint finite
sets V = V(G) of *nodes* and E = E(G) of *arcs*, and functions associating to each e ∈ E a
*tail* t(e) ∈ V and a *head* h(e) ∈ V."

The node set is the type `V`, the arc set the type `E` (finite where a statement needs it,
through `[Fintype V]`, `[Fintype E]`); `tail e` and `head e` are the tail and head of `e`.

**Formalization Note.** Loops (`tail e = head e`) and parallel arcs (distinct arcs with the same
tail and head) are allowed, as in the book (p. 19: a digraph is *simple* only if it has neither).
Disjointness of `V` and `E` is automatic for two types. -/
structure Digraph (V E : Type*) where
  /-- The tail `t(e)` of each arc. -/
  tail : E → V
  /-- The head `h(e)` of each arc. -/
  head : E → V

end CombOpt.ShortestPath


