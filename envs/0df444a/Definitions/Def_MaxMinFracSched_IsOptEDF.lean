-- Prove2me | Definitions.Def_MaxMinFracSched_IsOptEDF
-- name    : MaxMinFracSched_IsOptEDF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:43.365194+00:00
-- url     : https://prove2.me/theorems/f763798b-243b-4633-8fe9-a2aafffefa8a
-- title:
--   $\hat f$-EDF run
-- statement:
--   An **$\hat f$-EDF run** on the instance $J$ is a threshold-EDF run with thresholds $\theta_j(t)=\hat f_J\, w_j$: EDF applied to the works scaled by the offline optimum. By Observation 4.5 it is an optimal offline schedule.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Observation 4.5, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_optVal
import Definitions.Def_MaxMinFracSched_IsThresholdEDF

namespace MaxMinFracSched

/-- **An `f̂`-EDF run.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Observation 4.5, p.15 (PDF p.17): "OPT can be implemented by scaling
each job's work by f̂ and scheduling this work using EDF. We call this algorithm for OPT f̂-EDF."

A threshold-EDF run with threshold `f̂_J · w_j` (ties broken arbitrarily). -/
def IsOptEDF (J : Finset Job) (r : Job → ℝ → ℝ) : Prop :=
  IsThresholdEDF J (fun j _ => optVal J * j.w) r

end MaxMinFracSched


