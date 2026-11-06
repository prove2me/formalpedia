-- Prove2me | Definitions.Def_MaxMinFracSched_IsThresholdEDF
-- name    : MaxMinFracSched_IsThresholdEDF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:58.561318+00:00
-- url     : https://prove2.me/theorems/8707b4c0-8631-4ff5-8036-e63f90a46ce5
-- title:
--   Threshold-EDF run
-- statement:
--   Let $J$ be an instance and $\theta_j(t)$ thresholds. A schedule $r$ for $J$ is a **threshold-EDF run** if for almost every time $t$, writing
--   $$E(t)=\{\,j\in J : a_j\le t<d_j,\ c_j(t)<\theta_j(t)\,\}$$
--   for the eligible jobs:
--
--   1. if $E(t)=\emptyset$, every job of $J$ has rate $0$ at $t$ (the processor idles);
--   2. otherwise some $j\in E(t)$ of earliest deadline among $E(t)$ has rate $1$ at $t$ and every other job of $J$ has rate $0$.
--
--   EDF, $\hat f$-EDF and ScaledEDF are the threshold-EDF runs for the thresholds $w_j$, $\hat f_J w_j$ and $\alpha'\hat f_J(t)w_j$.
--
--   **Formalization Note** Ties among eligible jobs of earliest deadline are broken arbitrarily and independently at every time. A job is eligible only before its deadline. The rule is imposed for almost every $t$, since a schedule matters only up to null sets.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 4.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_IsSchedule
import Definitions.Def_MaxMinFracSched_work

namespace MaxMinFracSched

/-- **A threshold-EDF run.** The common shape of EDF (Lemma 3.3), `f̂`-EDF (Observation 4.5) and
ScaledEDF (Section 4.1). Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 4.1, p.14 (PDF p.16): "At any point in time t, ScaledEDF
(α′) works on the job with earliest deadline (breaking ties arbitrarily) among all jobs satisfying
ci < α′ · f̂(t) · wi. If there is no such job, ScaledEDF idles."

Given thresholds `θ j t`, a schedule `r` for `J` is a threshold-EDF run when, for almost every
time `t`, with `E t` the set of eligible jobs (`a_j ≤ t < d_j` and `c_j(t) < θ j t`):
1. if no job is eligible, every job of `J` has rate `0` at `t`;
2. otherwise some eligible job of earliest deadline among the eligible jobs has rate `1` at `t`
   and every other job of `J` has rate `0`.

**Formalization Note.** Ties are broken arbitrarily and independently at every time: any
eligible job of earliest deadline may be the one served. The condition is imposed for almost
every `t` (a schedule is determined only up to null sets). A job is eligible only before its
deadline. -/
def IsThresholdEDF (J : Finset Job) (θ : Job → ℝ → ℝ) (r : Job → ℝ → ℝ) : Prop :=
  IsSchedule J r ∧
    ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ((J.filter (fun j => j.a ≤ t ∧ t < j.d ∧ work r j t < θ j t)) = ∅ →
          ∀ j ∈ J, r j t = 0) ∧
      ((J.filter (fun j => j.a ≤ t ∧ t < j.d ∧ work r j t < θ j t)).Nonempty →
          ∃ j ∈ J.filter (fun j => j.a ≤ t ∧ t < j.d ∧ work r j t < θ j t),
            (∀ k ∈ J.filter (fun j => j.a ≤ t ∧ t < j.d ∧ work r j t < θ j t), j.d ≤ k.d) ∧
            r j t = 1 ∧ ∀ k ∈ J, k ≠ j → r k t = 0)

end MaxMinFracSched


