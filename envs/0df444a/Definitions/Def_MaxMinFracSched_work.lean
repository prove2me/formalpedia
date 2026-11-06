-- Prove2me | Definitions.Def_MaxMinFracSched_work
-- name    : MaxMinFracSched_work
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:00.800897+00:00
-- url     : https://prove2.me/theorems/3b5e5887-ee46-4aa7-9a9c-4aabde27703d
-- title:
--   Work completed by time $t$, $c_i(t)$
-- statement:
--   For a schedule $r$, a job $j$ and a time $t$,
--   $$c_j(t)=\int_{a_j}^{t} r_j(s)\,ds,$$
--   the work done on job $j$ between its arrival and time $t$.
--
--   **Formalization Note** The integral is the oriented interval integral; it is only used at times $t\ge a_j$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 3, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

/-- **Work completed by time `t`, `cᵢ(t)`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 3, p.12 (PDF p.14): "we define … ci(t)
as the total work completed for job i by time t."

`work r j t = ∫_{a_j}^{t} r j s ds`, the work the schedule `r` has done on job `j` between its
arrival and time `t`.

**Formalization Note.** Work before the arrival time is not counted. For `t < j.a` the oriented
interval integral is `-∫_t^{a_j}`; it is only ever evaluated at `t ≥ j.a` in a meaningful way. -/
noncomputable def work (r : Job → ℝ → ℝ) (j : Job) (t : ℝ) : ℝ :=
  ∫ s in j.a..t, r j s

end MaxMinFracSched


