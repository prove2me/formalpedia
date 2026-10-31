-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_IsDicircuit
-- name    : CombOpt_ShortestPath_Digraph_IsDicircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:52.314791+00:00
-- url     : https://prove2.me/theorems/456b7595-c967-4389-9d36-8976b94fa668
-- title:
--   Dicircuit
-- statement:
--   A path $v_0,e_1,v_1,\dots,e_k,v_k$ is **closed** if $v_0=v_k$, **edge-simple** if $e_1,\dots,e_k$ are distinct, and a **circuit** if it is edge-simple and closed, $v_0,\dots,v_{k-1}$ are distinct, and $k\ge1$. A **dicircuit** is a dipath that is also a circuit.
--
--   A loop $e$ with $t(e)=h(e)=v$ gives the dicircuit $v,e,v$ of length $1$.
--
--   **Formalization Note** `G.IsDicircuit u P` says that the arc list $P$ is a dipath from $u$ to $u$, nonempty, with distinct arcs, and with distinct nodes $v_0,\dots,v_{k-1}$; these are exactly the tails $t(e_1),\dots,t(e_k)$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19), circuits; §2.2, pp. 19–20 (PDF pp. 28–29), dicircuits

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsDipath

namespace CombOpt.ShortestPath

/-- **A dicircuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): a path P : v_0, e_1, v_1, …, e_k, v_k "is *closed* if v_0 = v_k;
it is *edge-simple* if e_1, …, e_k are distinct; … it is a *circuit* if it is edge-simple and
closed, v_0, …, v_{k−1} are distinct, and k ≥ 1"; §2.2, pp. 19–20 (PDF pp. 28–29): "A
*dicircuit* is a dipath that is also a circuit."

`G.IsDicircuit u P` says that `P` is a dipath from `u` back to `u` with at least one arc,
pairwise distinct arcs, and pairwise distinct nodes v_0, …, v_{k−1} (these are the tails of the
arcs of `P`).

**Formalization Note.** A loop (an arc `e` with `tail e = head e`) gives the dicircuit
`[e]` of length 1, as in the book. -/
def Digraph.IsDicircuit {V E : Type*} (G : Digraph V E) (u : V) (P : List E) : Prop :=
  G.IsDipath u P u ∧ P ≠ [] ∧ P.Nodup ∧ (P.map G.tail).Nodup

end CombOpt.ShortestPath


