-- Prove2me | Definitions.Def_CombOpt_Circulation_MultiDigraph
-- name    : CombOpt_Circulation_MultiDigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:19.868495+00:00
-- url     : https://prove2.me/theorems/5a906525-5004-4ae4-b285-3fa3b7074519
-- title:
--   Digraphs with loops and parallel arcs
-- statement:
--   A **digraph** $G=(V,E)$ consists of a set $V$ of nodes and a set $E$ of arcs, each arc $e$ having a tail $t(e)\in V$ and a head $h(e)\in V$. Loops ($t(e)=h(e)$) and parallel arcs (distinct arcs with the same tail and the same head) are allowed.
--
--   This is the graph model of every result in the mission.
--
--   **Formalization Note** Arcs are elements of an index type $E$ rather than pairs of nodes, which is what allows parallel arcs. Statements add finiteness of $V$ and $E$ as instance arguments, the book's graphs being finite.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 19 (PDF p. 28)

import Mathlib

namespace CombOpt.Circulation

universe u v

/-- A digraph in the sense of Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 19 (PDF p. 28): a set `V` of nodes and a set `E` of
arcs, each arc `e` having a tail `t(e)` and a head `h(e)`. Loops (`tail e = head e`) and parallel
arcs (distinct arcs with the same tail and head) are allowed.

**Formalization Note** Arcs are the elements of an index type `E`, not pairs of nodes; this is
what permits parallel arcs. The book's digraphs are finite: every statement of this mission adds
`[Fintype V] [Fintype E]`. -/
structure MultiDigraph (V : Type u) (E : Type v) where
  /-- The tail `t(e)` of an arc. -/
  tail : E → V
  /-- The head `h(e)` of an arc. -/
  head : E → V

end CombOpt.Circulation


