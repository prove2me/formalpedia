-- Prove2me | Definitions.Def_CombOpt_ShortestPath_pathCost
-- name    : CombOpt_ShortestPath_pathCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:21.479442+00:00
-- url     : https://prove2.me/theorems/84418d0a-a97c-4cca-a192-00a529c8fdec
-- title:
--   Cost $c(P)$ of a dipath
-- statement:
--   Given real arc costs $c=(c_e:e\in E)$, the **cost** of a dipath $P: v_0,e_1,v_1,\dots,e_k,v_k$ is
--   $$c(P)=\sum_{i=1}^k c_{e_i}.$$
--   An arc traversed several times is paid each time, and the one-node dipath ($k=0$) has cost $0$.
--
--   **Formalization Note** A dipath is represented by its list of arcs $[e_1,\dots,e_k]$, and the cost is the sum of $c$ over this list.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 20 (PDF p. 29), cost of a dipath

import Mathlib

namespace CombOpt.ShortestPath

/-- **The cost of a dipath.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 20 (PDF p. 29): "If each e ∈ E has a real cost c_e, the *cost* c(P) (with respect
to c) of the dipath P is defined to be Σ_{i=1}^k c_{e_i}."

`pathCost c P` is the sum of `c e` over the arcs of the list `P`, counted with multiplicity
(an arc used twice is paid twice); the empty dipath has cost `0`. -/
def pathCost {E : Type*} (c : E → ℝ) (P : List E) : ℝ :=
  (P.map c).sum

end CombOpt.ShortestPath


