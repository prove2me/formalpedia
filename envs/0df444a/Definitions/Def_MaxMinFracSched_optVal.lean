-- Prove2me | Definitions.Def_MaxMinFracSched_optVal
-- name    : MaxMinFracSched_optVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:37.130952+00:00
-- url     : https://prove2.me/theorems/14bc0d35-320e-4be5-a98e-567e4b31c77b
-- title:
--   Offline optimum $\hat f_J$
-- statement:
--   The **offline optimum** of the instance $J$ is
--   $$\hat f_J=\sup\Bigl\{\,v\in[0,1] : \text{some schedule } r \text{ for } J \text{ has } f_i\ge v \text{ for every } i\in J\,\Bigr\},$$
--   the best minimum fractional completion an offline scheduler that knows the whole instance can guarantee.
--
--   The set always contains $0$ and is bounded by $1$, so this is a genuine supremum; for the empty instance it equals $1$. Corollary 3.4 identifies it with $\min(1/\rho^\star,1)$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, Main problem definition, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_IsSchedule
import Definitions.Def_MaxMinFracSched_work
import Definitions.Def_MaxMinFracSched_frac

namespace MaxMinFracSched

/-- **The offline optimum `f̂_J`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3): "Let f̂J denote the objective
value achieved by an optimal offline scheduler that knows the entire instance in advance."

`optVal J` is the supremum of the values `v ∈ [0, 1]` such that some feasible schedule gives every
job of `J` fractional completion at least `v`.

**Formalization Note.** The set always contains `0` (the zero schedule) and is bounded by `1`, so
the supremum is a genuine supremum; fractional completions never exceed `1`, so the cap `v ≤ 1`
removes nothing for a nonempty instance. For `J = ∅` the value is `1`. The optimum is defined over
feasible schedules, not by the density formula (that is Corollary 3.4). -/
noncomputable def optVal (J : Finset Job) : ℝ :=
  sSup {v : ℝ | 0 ≤ v ∧ v ≤ 1 ∧ ∃ r, IsSchedule J r ∧ ∀ j ∈ J, v ≤ frac r j}

end MaxMinFracSched


