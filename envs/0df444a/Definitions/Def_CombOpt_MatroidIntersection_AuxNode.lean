-- Prove2me | Definitions.Def_CombOpt_MatroidIntersection_AuxNode
-- name    : CombOpt_MatroidIntersection_AuxNode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:40.432994+00:00
-- url     : https://prove2.me/theorems/1126c8c0-37c7-4c1a-96e7-9533d7e18770
-- title:
--   Nodes $S\cup\{r,s\}$ of the auxiliary digraph
-- statement:
--   The auxiliary digraph of matroid intersection has node set $S\cup\{r,s\}$: one node for each element of the ground set $S$, and two new nodes $r$ and $s$.
--
--   **Formalization Note** The nodes are `elem e` for $e\in S$, together with `r` and `s`; these are distinct from each other and from all `elem e`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.3, p. 290 (PDF p. 297)

import Mathlib

namespace CombOpt.MatroidIntersection

/-- **The node set `S ∪ {r, s}` of the auxiliary digraph.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.3,
p. 290 (PDF p. 297): "we define an auxiliary digraph G = G(M₁, M₂, J). It has node-set
S ∪ {r, s}".

`AuxNode S` has one node `elem e` for each element `e` of the ground set `S`, and two further
nodes `r` and `s`.

**Formalization Note.** `r` and `s` are new nodes, distinct from each other and from every
element of `S`, as the book intends. -/
inductive AuxNode (S : Type*) where
  /-- The node `r`. -/
  | r : AuxNode S
  /-- The node `s`. -/
  | s : AuxNode S
  /-- The node of the element `e ∈ S`. -/
  | elem (e : S) : AuxNode S

end CombOpt.MatroidIntersection


