-- Prove2me | Definitions.Def_MaxMinFracSched_ScaledNeverIdle
-- name    : MaxMinFracSched_ScaledNeverIdle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:37.598209+00:00
-- url     : https://prove2.me/theorems/fcb6a464-066f-413a-93b4-2dd94ec089e5
-- title:
--   The run is never idle
-- statement:
--   The run $r$ on the instance $J$ is **never idle** if $\sum_{j\in J} r_j(t)=1$ at almost every time $t$ between the first arrival and the final deadline of $J$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Lemma 4.7, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_minArr
import Definitions.Def_MaxMinFracSched_maxDl

namespace MaxMinFracSched

/-- **ScaledEDF is never idle.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Lemma 4.7, p.16 (PDF p.18): "on J′, ScaledEDF is never
idle".

The run `r` keeps the processor fully busy at almost every time between the first arrival and
the final deadline of `J`. -/
def ScaledNeverIdle (J : Finset Job) (r : Job → ℝ → ℝ) : Prop :=
  ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    t ∈ Set.Icc (minArr J) (maxDl J) → ∑ j ∈ J, r j t = 1

end MaxMinFracSched


