-- Prove2me | Definitions.Def_IPMJumpLB_IsFlowFeasible
-- name    : IPMJumpLB_IsFlowFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:32.499083+00:00
-- url     : https://prove2.me/theorems/9db6edf8-d624-4aed-b833-618a269eb371
-- title:
--   Flow conservation $B^\top f = d$
-- statement:
--   A vector $f \in \mathbb R^E$ satisfies **flow conservation** for a min-cost flow instance with demands $d$ if at every vertex $u$
--   $$
--   \sum_{e = (u, v) \in E} f_e - \sum_{e = (v, u) \in E} f_e = d_u ,
--   $$
--   i.e. the net outflow $B^\top f$ equals the demand vector. Sign conditions on $f$ ($f \ge 0$ or $f > 0$) are imposed separately.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 2, p.3 (B⊤f = d), restated per vertex in Section 3.1, p.6

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance

namespace IPMJumpLB

/-- Flow conservation `B⊤f = d` (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §2, p.3, restated per vertex in §3.1, p.6): at every vertex
`u`, the flow on the arcs leaving `u` minus the flow on the arcs entering `u` equals the demand
`d_u`. Nonnegativity or positivity of `f` is a separate condition. -/
def IsFlowFeasible {V E : Type*} [Fintype E] [DecidableEq V] (I : FlowInstance V E)
    (f : E → ℝ) : Prop :=
  ∀ u : V, (∑ e ∈ Finset.univ.filter (fun e => I.tail e = u), f e)
      - (∑ e ∈ Finset.univ.filter (fun e => I.head e = u), f e) = I.demand u

end IPMJumpLB


