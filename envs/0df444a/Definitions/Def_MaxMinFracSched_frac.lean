-- Prove2me | Definitions.Def_MaxMinFracSched_frac
-- name    : MaxMinFracSched_frac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:38.006605+00:00
-- url     : https://prove2.me/theorems/562b13c5-659c-425b-a77c-70f1d8ff81fa
-- title:
--   Fractional completion $f_i=c_i/w_i$
-- statement:
--   The **fractional completion** of job $j$ under the schedule $r$ is
--   $$f_j=\frac{\min\bigl(w_j,\ c_j(d_j)\bigr)}{w_j},$$
--   the work done on $j$ between its arrival and its deadline, capped at $w_j$, as a fraction of its work requirement. For a valid job it lies in $[0,1]$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, Main problem definition, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_work

namespace MaxMinFracSched

/-- **Fractional completion `fᵢ = cᵢ / wᵢ`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3): "Let ci ≤ wi denote
the amount of work completed on job i by its deadline. The fractional completion of job i is
fi := ci/wi."

`frac r j = min(w_j, c_j(d_j)) / w_j`: the work done on `j` between its arrival and its deadline,
capped at `w_j`, divided by `w_j`.

**Formalization Note.** Work after the deadline is not counted, and work beyond `w_j` is capped
(`cᵢ ≤ wᵢ`). For a valid job (`a < d`, `0 < w`) the value lies in `[0, 1]`. -/
noncomputable def frac (r : Job → ℝ → ℝ) (j : Job) : ℝ :=
  min j.w (work r j j.d) / j.w

end MaxMinFracSched


