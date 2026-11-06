-- Prove2me | Definitions.Def_IPMJumpLB_gap
-- name    : IPMJumpLB_gap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:11.594792+00:00
-- url     : https://prove2.me/theorems/3ad3b98f-b501-44f7-9aca-3ab27bf7cc9f
-- title:
--   Duality gap $D(s, f) = \langle s, f\rangle$
-- statement:
--   For a potential vector $x$ with slacks $s = c - Bx$ and a flow $f$, the **duality gap** is
--   $$
--   D(s, f) = \langle s, f\rangle = \sum_{e \in E} s_e f_e .
--   $$
--   For primal feasible $f$ and dual feasible $x$ it equals $\langle c, f\rangle - \langle d, x\rangle$.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 2, p.3 (below (1))

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack

namespace IPMJumpLB

/-- The duality gap `D(s, f) = ⟨s, f⟩ = ∑_e s_e f_e` of a potential vector `x` (with slacks
`s = c − Bx`) and a flow `f` (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §2, p.3, below (1)). -/
noncomputable def gap {V E : Type*} [Fintype E] (I : FlowInstance V E) (x : V → ℝ)
    (f : E → ℝ) : ℝ :=
  ∑ e, slack I x e * f e

end IPMJumpLB


