-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_queueLaw
-- name    : CrossLayerControl_ECCA_queueLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:45:53.162345+00:00
-- url     : https://prove2.me/theorems/3399d20d-b7f5-431c-99f9-8acf18f44877
-- title:
--   The single-queue law $U(t+1)=\max[U(t)-\mu(t),0]+A(t)$
-- statement:
--   For an initial backlog $u_0$, a service process $\mu(t)$ and an arrival process $A(t)$, the backlog evolves by
--   $$U(0)=u_0,\qquad U(t+1)=\max[U(t)-\mu(t),0]+A(t).$$
--
--   Arrivals of slot $t$ occur at the end of the slot and cannot be served in it. Every queue of the paper, real or virtual, follows this law.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, §3.1, p. 23

import Mathlib

namespace CrossLayerControl.ECCA

/-- **The single-queue law of §3.1.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), §3.1, p. 23 (unnumbered): "Consider a single queue with an input
process A(t) and transmission rate process µ(t), where A(t) represents the amount of new arrivals
that enter the queue during slot t, and µ(t) represents the transmission rate of the server during
slot t. We assume that the A(t) arrivals occur at the end of slot t, so that they cannot be
transmitted during that slot. Let U(t) represent the current backlog in the queue. The U(t)
process evolves according to the following discrete time queueing law:
U(t + 1) = max[U(t) − µ(t), 0] + A(t)."

`queueLaw u₀ μ A t` is the backlog `U(t)` started from `U(0) = u₀`, with service process `μ` and
arrival process `A`: `U(0) = u₀` and `U(t + 1) = max (U(t) − μ(t)) 0 + A(t)`. -/
noncomputable def queueLaw (u₀ : ℝ) (μ A : ℕ → ℝ) : ℕ → ℝ
  | 0 => u₀
  | t + 1 => max (queueLaw u₀ μ A t - μ t) 0 + A t

end CrossLayerControl.ECCA


