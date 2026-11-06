-- Prove2me | Definitions.Def_MaxMinFracSched_IsSchedule
-- name    : MaxMinFracSched_IsSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:00.842497+00:00
-- url     : https://prove2.me/theorems/bd67d752-843c-45a9-9829-8e1b76c2f06c
-- title:
--   Feasible single-processor (rate) schedule
-- statement:
--   A **schedule** for the instance $J$ is a family of processing rates $r_j(t)$, the rate at which job $j$ is processed at time $t$, such that
--
--   1. $r_j(t)\ge 0$ for all $j,t$;
--   2. $\sum_{j\in J} r_j(t)\le 1$ for every $t$ (one unit-speed processor);
--   3. every $t\mapsto r_j(t)$ is measurable.
--
--   Preemptive one-job-at-a-time schedules are the schedules with rates in $\{0,1\}$.
--
--   **Formalization Note** Rate schedules (processor sharing) generalize the paper's preemptive schedules. They do not change the offline optimum, which EDF on the scaled works attains (Corollary 3.4), and they enlarge the class of online algorithms, which makes the impossibility result stronger.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, Main problem definition, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

/-- **A feasible single-processor schedule.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3): "A schedule executes
these jobs on a single processor, with preemption permitted: the execution of a job may be
interrupted in order to execute some other job(s) and resumed at some later time."

A schedule for the instance `J` is a family of processing rates `r j t` (the rate at which job `j`
is processed at time `t`) such that every rate is nonnegative, the rates of the jobs of `J` sum to
at most `1` at every time, and every `r j` is measurable.

**Formalization Note.** Rate schedules generalize preemptive single-job schedules (the
`{0,1}`-valued case). Fractional sharing of the processor does not change the offline optimum
(EDF on the scaled works attains it, Corollary 3.4), and it enlarges the class of online
algorithms. Rates of jobs outside `J` are irrelevant to every quantity built on a schedule. -/
def IsSchedule (J : Finset Job) (r : Job → ℝ → ℝ) : Prop :=
  (∀ j t, 0 ≤ r j t) ∧ (∀ t, ∑ j ∈ J, r j t ≤ 1) ∧ ∀ j, Measurable (r j)

end MaxMinFracSched


