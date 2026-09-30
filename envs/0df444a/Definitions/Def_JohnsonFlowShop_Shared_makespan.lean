-- Prove2me | Definitions.Def_JohnsonFlowShop_Shared_makespan
-- name    : JohnsonFlowShop_Shared_makespan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:35:35.781004+00:00
-- url     : https://prove2.me/theorems/4c83ffe5-5310-4b86-8d7c-95af33681521
-- title:
--   Total elapsed time (makespan) of a schedule (p. 61)
-- statement:
--   For a schedule whose last machine has start times $s_i$ and processing times $P_i$ (item $i$), the **total elapsed time** is the time at which the last item leaves the last machine:
--   $$
--   T(s) = \max\Bigl(0,\ \max_{i} \bigl(s_i + P_i\bigr)\Bigr).
--   $$
--   It is the objective Johnson's problems minimize ("minimize the total elapsed time").
--
--   It serves both missions of the series: `01-two-stage` (p. 61, PDF p. 1, Two-stage production schedule, "minimize the total elapsed time"; applied to the machine-2 start times $s^2_i$ and times $B_i$) and `02-three-stage` (p. 61, PDF p. 1, and p. 65, PDF p. 5, Three-stage production schedule; applied to the machine-3 start times $s^3_i$ and times $C_i$). It is reviewed once for both.
--
--   **Formalization Note** The maximum is `Finset.univ.fold max 0`, so the empty instance ($n = 0$) has total elapsed time $0$. For a feasible schedule with positive processing times every completion time $s_i + P_i$ is positive, so the extra $0$ does not change the value when $n \ge 1$.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 61, Two-stage production schedule ("minimize the total elapsed time"); p. 65, Three-stage production schedule

import Mathlib

namespace JohnsonFlowShop.Shared

/-- The total elapsed time (makespan) of a schedule: the latest completion time
`max_i (s₂ i + B i)` on the last machine (machine 2 of a two-machine schedule, machine 3 of a
three-machine schedule), `s₂ i` being item `i`'s start time and `B i` its processing time on that
machine, taken together with `0` (so the empty instance `n = 0` has makespan `0`; for a feasible
schedule with positive times every completion time is positive, so the `0` never matters). -/
def makespan {n : ℕ} (B : Fin n → ℝ) (s₂ : Fin n → ℝ) : ℝ :=
  Finset.univ.fold max 0 (fun i => s₂ i + B i)

end JohnsonFlowShop.Shared


