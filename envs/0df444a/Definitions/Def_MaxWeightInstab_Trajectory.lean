-- Prove2me | Definitions.Def_MaxWeightInstab_Trajectory
-- name    : MaxWeightInstab_Trajectory
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:52.778368+00:00
-- url     : https://prove2.me/theorems/76a01089-4c12-41cd-8682-4bd4cd737314
-- title:
--   Sample path of the MaxWeight queueing process
-- statement:
--   A **trajectory** of the network of Figure 1 under MaxWeight consists of queue lengths $Q(t)$, the schedule $\sigma(t+1)$ used in time unit $t+1$, and the external arrivals $e(t+1)$ of time unit $t+1$, such that for every $t\ge0$:
--
--   1. $\sigma(t+1)$ is a MaxWeight schedule for $Q(t)$ ("the allocation of service at time $t$ is governed by $Q(t-1)$", p.5), ties broken in any way;
--   2. $Q(t+1)$ is obtained from $Q(t)$ by one time unit with schedule $\sigma(t+1)$ and arrivals $e(t+1)$.
--
--   Lemmas 2–7 and Proposition 1 are statements about every such path whose arrivals lie in $G_M$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, pp.1, 3, 5

import Mathlib
import Definitions.Def_MaxWeightInstab_IsMaxWeight
import Definitions.Def_MaxWeightInstab_step

namespace MaxWeightInstab

/-- A sample path of the queueing network process of Figure 1 under MaxWeight with arbitrary tie
choices (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, pp.1, 3, 5): queue lengths `Q t`, the schedule `σ (t+1)` used in time unit `t+1`
and the external arrivals `e (t+1)` of time unit `t+1`. The schedule of time unit `t+1` is a
maximizer of (1) for `Q(t)` ("The allocation of service at time t is governed by Q(t − 1)", p.5),
and `Q(t+1)` is obtained from `Q(t)` by serving first and then adding arrivals.

**Formalization Note.** `σ 0` and `e 0` carry no meaning. Lemmas 2–7 and Proposition 1 are
statements about every such path whose arrivals satisfy `G_M`, whatever the tie choices. -/
structure Trajectory (J ν : ℕ) where
  /-- The queue lengths `Q(t)`. -/
  Q : ℕ → State J
  /-- The schedule used in time unit `t` (`t ≥ 1`). -/
  σ : ℕ → State J
  /-- The external arrivals of time unit `t` (`t ≥ 1`). -/
  e : ℕ → ExtArrivals J
  /-- The schedule of time unit `t+1` solves (1) for `Q(t)`. -/
  maxWeight : ∀ t, IsMaxWeight ν (Q t) (σ (t + 1))
  /-- Serve, then add arrivals. -/
  step_eq : ∀ t, Q (t + 1) = step (Q t) (σ (t + 1)) (e (t + 1))

end MaxWeightInstab


