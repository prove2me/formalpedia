-- Prove2me | Definitions.Def_MaxMinFracSched_ScaledFails
-- name    : MaxMinFracSched_ScaledFails
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:26.460696+00:00
-- url     : https://prove2.me/theorems/c9669fac-269d-49c1-86df-12025c81aa4a
-- title:
--   Run not $\alpha'$-competitive
-- statement:
--   The run $r$ on the instance $J$ is **not $\alpha'$-competitive** if some job $j\in J$ has
--   $$f_j<\alpha'\cdot\hat f_J .$$
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Definition 4.4, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_frac
import Definitions.Def_MaxMinFracSched_optVal

namespace MaxMinFracSched

/-- **The run is not α′-competitive.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Definition 4.4 (Harder instance), p.15 (PDF p.17):
"Consider an instance J where ScaledEDF is not α′-competitive."

Some job of `J` receives fractional completion below `α′ · f̂_J` in the run `r`. -/
def ScaledFails (α' : ℝ) (J : Finset Job) (r : Job → ℝ → ℝ) : Prop :=
  ∃ j ∈ J, frac r j < α' * optVal J

end MaxMinFracSched


