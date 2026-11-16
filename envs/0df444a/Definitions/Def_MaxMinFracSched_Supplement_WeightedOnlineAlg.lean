-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_WeightedOnlineAlg
-- name    : MaxMinFracSched_Supplement_WeightedOnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:11:59.337943+00:00
-- url     : https://prove2.me/theorems/70238164-feb4-4d7f-bb17-4507a2a3cdf7
-- title:
--   Deterministic online algorithm for the weighted problem
-- statement:
--   A **deterministic weighted online algorithm** maps every instance $J$ with weights $\lambda$ to a feasible schedule $A(\lambda,J)$ and is **causal**: whenever two weighted instances $(J,\lambda)$ and $(J',\lambda')$ have the same jobs released by time $t$, $J_{\le t}=J'_{\le t}$, with the same weights on those jobs, then on every released job the two schedules have done the same work by every time $s\le t$.
--
--   This models an algorithm that learns each job's arrival time, deadline, work and weight only at the job's arrival (Section 1).
--
--   **Formalization Note** The causality convention is the one of the base mission's `OnlineAlg`, cumulative work on released jobs, with the weights added. Schedules are rate schedules.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_pre
import Definitions.Def_MaxMinFracSched_IsSchedule
import Definitions.Def_MaxMinFracSched_work

namespace MaxMinFracSched

namespace Supplement

/-- **A deterministic online algorithm for the weighted problem.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3): "each job i has a positive weight λi, revealed online along
with the rest of the job", and "Nothing is known about the job i until its arrival time ai".

The weights are part of the input: `sched lam J` is the schedule produced on the instance `J` with
weights `lam`; it is feasible, and it is causal: if two weighted instances have the same jobs
released by time `t`, with the same weights on those jobs, then on each released job the algorithm
has done the same cumulative work at every time `s ≤ t`.

**Formalization Note.** The same causality convention as the base `OnlineAlg` (cumulative work
on the released jobs), extended by the weights, which are revealed at arrival. Weights of jobs not
yet released cannot influence the past. -/
structure WeightedOnlineAlg where
  /-- the schedule produced on each weighted instance -/
  sched : (Job → ℝ) → Finset Job → Job → ℝ → ℝ
  /-- every produced schedule is feasible -/
  feasible : ∀ lam J, IsSchedule J (sched lam J)
  /-- the work done by time `t` depends only on the jobs released by `t` and their weights -/
  causal : ∀ (lam lam' : Job → ℝ) (J J' : Finset Job) (t : ℝ), pre J t = pre J' t →
    (∀ j ∈ pre J t, lam j = lam' j) →
    ∀ j ∈ pre J t, ∀ s ≤ t, work (sched lam J) j s = work (sched lam' J') j s

end Supplement

end MaxMinFracSched


