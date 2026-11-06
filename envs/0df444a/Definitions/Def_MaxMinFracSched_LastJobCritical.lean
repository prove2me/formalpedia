-- Prove2me | Definitions.Def_MaxMinFracSched_LastJobCritical
-- name    : MaxMinFracSched_LastJobCritical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:04.556204+00:00
-- url     : https://prove2.me/theorems/c0db4996-05aa-4d23-8daf-f573493885a1
-- title:
--   Last job critical
-- statement:
--   The run $r$ on the instance $J$ has the **last job critical** property if some job $\ell\in J$ of latest deadline ($d_j\le d_\ell$ for all $j\in J$) has
--   $$f_\ell<\alpha'\cdot\hat f_J ,$$
--   i.e. the run fails to complete an $\alpha'\hat f$ fraction of the latest-deadline job.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 4.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_frac
import Definitions.Def_MaxMinFracSched_optVal

namespace MaxMinFracSched

/-- **The last job is critical.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 4.2, p.15 (PDF p.17): "The last job is critical,
i.e. ScaledEDF fails to complete an α′ · f̂ fraction of the latest deadline job".

Some job of latest deadline in `J` receives fractional completion below `α′ · f̂_J` in the run
`r`. -/
def LastJobCritical (α' : ℝ) (J : Finset Job) (r : Job → ℝ → ℝ) : Prop :=
  ∃ ℓ ∈ J, (∀ j ∈ J, j.d ≤ ℓ.d) ∧ frac r ℓ < α' * optVal J

end MaxMinFracSched


