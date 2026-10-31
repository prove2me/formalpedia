-- Prove2me | Definitions.Def_CombOpt_MinCut_CapGraph_uSum
-- name    : CombOpt_MinCut_CapGraph_uSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:56.390991+00:00
-- url     : https://prove2.me/theorems/6832c701-6dcc-43e8-8d4f-6da359fa6c40
-- title:
--   Capacity $u(A)=\sum_{e\in A}u_e$ of an edge set
-- statement:
--   For a capacitated graph $G$ and a finite set $A$ of edges, the **capacity** of $A$ is
--
--   $$u(A)=\sum_{e\in A}u_e .$$
--
--   It is used as $u(\delta(S))$, the capacity of a cut, and as $u(\delta(V_{i-1})\cap\delta(v_j))$ in the definition of a legal ordering.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), notation x(A) = Σ_{e∈A} x_e; used as u(δ(S)) in §3.5, p. 72 (PDF p. 81)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph

namespace CombOpt.MinCut

/-- **The capacity `u(A) = Σ_{e ∈ A} u_e` of an edge set `A`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1
(the notation `x(A)` for `Σ_{e∈A} x_e`), used as `u(δ(S))` in §3.5, p. 72 (PDF p. 81). -/
def CapGraph.uSum {V E : Type*} (G : CapGraph V E) (A : Finset E) : ℝ :=
  ∑ e ∈ A, G.u e

end CombOpt.MinCut


