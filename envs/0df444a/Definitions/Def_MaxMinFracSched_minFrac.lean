-- Prove2me | Definitions.Def_MaxMinFracSched_minFrac
-- name    : MaxMinFracSched_minFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:32.682574+00:00
-- url     : https://prove2.me/theorems/a8f7b52a-464e-43dd-9726-97bb160c2bed
-- title:
--   Objective value $f_J=\min_{i\in J} f_i$
-- statement:
--   The **objective value** of a schedule $r$ on the instance $J$ is the minimum fractional completion
--   $$f_J=\min_{i\in J} f_i .$$
--
--   **Formalization Note** It is written as an infimum over the jobs of $J$ and is only used for nonempty $J$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, Main problem definition, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_work
import Definitions.Def_MaxMinFracSched_frac

namespace MaxMinFracSched

/-- **The objective value `f_J = min_{i∈J} fᵢ`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3): "The objective
value of a schedule on instance J is the minimum fractional completion over all jobs, denoted
fJ := mini∈J fi."

**Formalization Note.** An `iInf` over the jobs of `J`; it is the minimum for nonempty `J` and is
only used for valid (hence nonempty) instances. -/
noncomputable def minFrac (J : Finset Job) (r : Job → ℝ → ℝ) : ℝ :=
  ⨅ j : J, frac r (j : Job)

end MaxMinFracSched


