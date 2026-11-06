-- Prove2me | Definitions.Def_MaxMinFracSched_IsScaledEDF
-- name    : MaxMinFracSched_IsScaledEDF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:52.90361+00:00
-- url     : https://prove2.me/theorems/248dfea7-108c-4998-aae0-b2e0444cb85d
-- title:
--   ScaledEDF$(\alpha')$ run
-- statement:
--   A **ScaledEDF$(\alpha')$ run** on the instance $J$ is a threshold-EDF run with thresholds
--   $$\theta_j(t)=\alpha'\cdot\hat f_J(t)\cdot w_j .$$
--   At every time it works on an earliest-deadline job among the released, unexpired jobs $j$ with $c_j(t)<\alpha'\hat f_J(t)w_j$ (ties broken arbitrarily), and idles if there is none.
--
--   **Formalization Note** The threshold uses the running optimum $\hat f_J(t)$ of the jobs released so far, never the final $\hat f_J$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 4.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_optAt
import Definitions.Def_MaxMinFracSched_IsThresholdEDF

namespace MaxMinFracSched

/-- **A ScaledEDF(α′) run.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 4.1, p.14 (PDF p.16): "At any point in time t,
ScaledEDF (α′) works on the job with earliest deadline (breaking ties arbitrarily) among all jobs
satisfying ci < α′ · f̂(t) · wi. If there is no such job, ScaledEDF idles."

A threshold-EDF run with threshold `α′ · f̂_J(t) · w_j`, where `f̂_J(t) = optAt J t` is the
offline optimum of the jobs released by time `t`.

**Formalization Note.** Any tie-breaking at any time is allowed (see `IsThresholdEDF`). The
threshold uses the running optimum `f̂_J(t)`, never the final `f̂_J`. -/
def IsScaledEDF (α' : ℝ) (J : Finset Job) (r : Job → ℝ → ℝ) : Prop :=
  IsThresholdEDF J (fun j t => α' * optAt J t * j.w) r

end MaxMinFracSched


