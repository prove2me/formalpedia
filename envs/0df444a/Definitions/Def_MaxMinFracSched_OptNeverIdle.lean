-- Prove2me | Definitions.Def_MaxMinFracSched_OptNeverIdle
-- name    : MaxMinFracSched_OptNeverIdle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:37.441212+00:00
-- url     : https://prove2.me/theorems/0c0af253-6ade-4ca2-b0ad-edb9d77b62c4
-- title:
--   OPT (as $\hat f$-EDF) is never idle
-- statement:
--   The instance $J$ has **OPT never idle** if every $\hat f$-EDF run of $J$ keeps the processor fully busy, $\sum_{j\in J} r_j(t)=1$, at almost every time $t$ between the first arrival and the final deadline of $J$.
--
--   **Formalization Note** The paper's horizon $[0,T]$ is the interval from the first arrival to the final deadline.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Lemma 4.6, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_IsOptEDF
import Definitions.Def_MaxMinFracSched_minArr
import Definitions.Def_MaxMinFracSched_maxDl

namespace MaxMinFracSched

/-- **OPT (as scheduled by `f̂`-EDF) is never idle.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Lemma 4.6, p.15 (PDF p.17): "a harder
instance J′ where OPT (as scheduled by f̂-EDF) is never idle".

Every `f̂`-EDF run of `J` keeps the processor fully busy at almost every time between the first
arrival and the final deadline.

**Formalization Note.** The paper's horizon `[0, T]` is `[minArr J, maxDl J]` once the clock
starts at the first arrival. -/
def OptNeverIdle (J : Finset Job) : Prop :=
  ∀ r, IsOptEDF J r → ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    t ∈ Set.Icc (minArr J) (maxDl J) → ∑ j ∈ J, r j t = 1

end MaxMinFracSched


