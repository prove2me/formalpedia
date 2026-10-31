-- Prove2me | Definitions.Def_CombOpt_MatroidIntersection_innerElems
-- name    : CombOpt_MatroidIntersection_innerElems
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:27.388+00:00
-- url     : https://prove2.me/theorems/2baca668-b8fa-48c2-a3d2-541f3c22a8ae
-- title:
--   Elements of $S$ on a node sequence
-- statement:
--   For the node sequence $r,e_1,f_1,\dots,e_m,f_m,e_{m+1},s$ of an $(r,s)$-dipath in the auxiliary digraph, this is the set $\{e_1,f_1,\dots,e_m,f_m,e_{m+1}\}\subseteq S$ of elements of the ground set visited by the path.
--
--   **Formalization Note** For any list of nodes of the auxiliary digraph, `innerElems P` is the finite set of $e\in S$ whose node occurs in $P$; the nodes $r$ and $s$ are dropped.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.3, p. 291 (PDF p. 298)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_AuxNode

namespace CombOpt.MatroidIntersection

/-- **The elements of `S` on a node sequence of the auxiliary digraph.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.3,
p. 291 (PDF p. 298): for the node sequence r, e₁, f₁, …, e_m, f_m, e_{m+1}, s of an
(r, s)-dipath, the set {e₁, f₁, …, e_m, f_m, e_{m+1}}.

`innerElems P` is the set of elements `e ∈ S` whose node `elem e` occurs in the list `P`; the
nodes `r` and `s` are dropped.

**Formalization Note.** The result is a `Finset S` (repetitions are forgotten). -/
def innerElems {S : Type*} [DecidableEq S] (P : List (AuxNode S)) : Finset S :=
  (P.filterMap fun x => match x with
    | .elem e => some e
    | _ => none).toFinset

end CombOpt.MatroidIntersection


