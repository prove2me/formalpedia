-- Prove2me | Definitions.Def_MaxMinFracSched_OnlineAlg
-- name    : MaxMinFracSched_OnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:52.495381+00:00
-- url     : https://prove2.me/theorems/7e05ee36-cf21-4389-b63a-0f2ed936c12a
-- title:
--   Deterministic online scheduling algorithm
-- statement:
--   A **deterministic online algorithm** assigns to every instance $J$ a schedule $\mathrm{ALG}(J)$ such that
--
--   1. $\mathrm{ALG}(J)$ is feasible for $J$;
--   2. (causality) if $J_{\le t}=J'_{\le t}$, then for every job $j\in J_{\le t}$ and every $s\le t$ the work done on $j$ by time $s$ is the same in $\mathrm{ALG}(J)$ and in $\mathrm{ALG}(J')$.
--
--   Causality expresses "nothing is known about job $i$ until its arrival time $a_i$": what the algorithm has done by time $t$ depends only on the jobs released by $t$.
--
--   **Formalization Note** Causality is stated on the cumulative work of the released jobs, the weakest form, so the class of online algorithms is as large as possible.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, Main problem definition, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_pre
import Definitions.Def_MaxMinFracSched_IsSchedule
import Definitions.Def_MaxMinFracSched_work

namespace MaxMinFracSched

/-- **A deterministic online scheduling algorithm.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3): "The input is
a set J of n jobs that arrive online. … Nothing is known about the job i until its arrival time
ai; at time Ai, all three parameters become known."

An online algorithm maps every instance `J` to a feasible schedule `sched J`, and is causal: if
two instances have the same jobs released by time `t`, then on each of those jobs the algorithm
has done the same cumulative work at every time `s ≤ t`.

**Formalization Note.** Causality is stated on cumulative work of the released jobs, the weakest
form of "the algorithm's past cannot depend on future arrivals"; this makes the class of online
algorithms as large as possible. -/
structure OnlineAlg where
  /-- the schedule produced on each instance -/
  sched : Finset Job → Job → ℝ → ℝ
  /-- every produced schedule is feasible -/
  feasible : ∀ J, IsSchedule J (sched J)
  /-- the work done by time `t` depends only on the jobs released by time `t` -/
  causal : ∀ (J J' : Finset Job) (t : ℝ), pre J t = pre J' t →
    ∀ j ∈ pre J t, ∀ s ≤ t, work (sched J) j s = work (sched J') j s

end MaxMinFracSched


