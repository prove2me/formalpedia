-- Prove2me | Definitions.Def_NetworkControl_CapacityRegion_QueueBacklog
-- name    : NetworkControl_CapacityRegion_QueueBacklog
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:18:55.830494+00:00
-- url     : https://prove2.me/theorems/0833d1de-fee4-480e-8321-85e3410488d7
-- title:
--   Discrete-time queueing law, U(t+1) = max[U(t)-μ(t),0] + A(t) (p. 23)
-- statement:
--   The book's queueing recursion, stated in prose at the start of §3.1 (p. 23), just before
--   Definition 3.1: given an arrival process $A$, a service (transmission-rate) process $\mathrm{svc}$
--   and an initial backlog $U_0$ on a common sample space $\Omega$, the backlog evolves as
--   $U(t+1)=\max[U(t)-\mathrm{svc}(t),0]+A(t)$, pointwise on $\Omega$, for every $t\ge0$.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 23, Section 3.1 (unnumbered display equation, immediately preceding Definition 3.1)

import Mathlib

namespace NetworkControl.CapacityRegion

/-- The discrete-time queueing law stated at the start of Section 3.1 (p. 23):
`U(t+1) = max[U(t) - μ(t), 0] + A(t)`, for an arrival process `A`, a service process `svc`,
and an initial backlog `U0`, all on a common sample space `Ω`. -/
def QueueBacklog {Ω : Type*} (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => U0
  | t + 1 => fun ω => max (QueueBacklog A svc U0 t ω - svc t ω) 0 + A t ω

end NetworkControl.CapacityRegion


