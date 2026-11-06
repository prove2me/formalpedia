-- Prove2me | Definitions.Def_MaxMinFracSched_hardJob
-- name    : MaxMinFracSched_hardJob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:24.800719+00:00
-- url     : https://prove2.me/theorems/c650ff49-e2de-4783-aef4-d33b3a0bb54b
-- title:
--   Hard family: the job released at $t_i$, due at $t_j$
-- statement:
--   The job of the hard family released at $t_i$ and due at $t_j$: arrival $t_i$, deadline $t_j$, work $w_i(j)$, labelled by the Cantor pairing of $(i,j)$ so that distinct index pairs give distinct jobs.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 6.1, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_tt
import Definitions.Def_MaxMinFracSched_hw

namespace MaxMinFracSched

/-- **The job of the hard family released at `t_i` and due at `t_j`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 6.1, p.29
(PDF p.31): "for each j > i, it releases a job due at tj with weight wi(j)".

`hardJob x k i j = ⟨pair(i, j), t_i, t_j, w_i(j)⟩`, labelled by the Cantor pairing of `(i, j)`
so that distinct index pairs give distinct jobs. -/
noncomputable def hardJob (x : ℝ) (k i j : ℕ) : Job :=
  ⟨Nat.pair i j, tt x k i, tt x k j, hw x k i j⟩

end MaxMinFracSched


