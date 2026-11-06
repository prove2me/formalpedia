-- Prove2me | Definitions.Def_IPMJumpLB_slack
-- name    : IPMJumpLB_slack
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:14.865826+00:00
-- url     : https://prove2.me/theorems/3ccfb961-6ffb-4f78-94c0-ae367772a150
-- title:
--   Dual slack $s = c - Bx$
-- statement:
--   For a min-cost flow instance with costs $c$ and a potential vector $x \in \mathbb R^V$, the **dual slack** of an arc $e = (u, v)$ is
--   $$
--   s_e = c_e - x_u + x_v ,
--   $$
--   that is, $s = c - Bx$ for the arc-vertex incidence matrix $B$, whose row for $e = (u, v)$ has $+1$ at the tail $u$ and $-1$ at the head $v$. Dual feasibility of $x$ is $s \ge 0$ and strict dual feasibility is $s > 0$.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 2, p.3

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance

namespace IPMJumpLB

/-- The dual slack `s := c − Bx` of a potential vector `x ∈ ℝ^V` (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §2, p.3):
`s_e = c_e − x_u + x_v` for an arc `e = (u, v)` (tail `u`, head `v`). -/
def slack {V E : Type*} (I : FlowInstance V E) (x : V → ℝ) (e : E) : ℝ :=
  I.cost e - x (I.tail e) + x (I.head e)

end IPMJumpLB


