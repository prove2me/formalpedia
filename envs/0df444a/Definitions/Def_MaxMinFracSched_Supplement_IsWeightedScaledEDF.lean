-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_IsWeightedScaledEDF
-- name    : MaxMinFracSched_Supplement_IsWeightedScaledEDF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:11:35.322731+00:00
-- url     : https://prove2.me/theorems/3f0c4321-d3d0-44cc-bb47-6b01670e7a74
-- title:
--   A WeightedScaledEDF$(\alpha^{\prime})$ run with a fixed tie-breaking order
-- statement:
--   Fix weights $\lambda$, a parameter $\alpha'$ and a priority relation $\prec$ on jobs. A schedule $r$ of the instance $J$ is a **WeightedScaledEDF$(\alpha')$ run for $\prec$** when it is feasible and, for almost every time $t$, the following holds. Call a job $j\in J$ **eligible** at $t$ when $a_j\le t<d_j$ and
--   $$
--   c_j(t)<\theta_j(t):=\alpha'\cdot\hat f^{\lambda}_J(t)\cdot\frac{w_j}{\lambda_j},
--   $$
--   where $c_j(t)$ is the work done on $j$ by time $t$ and $\hat f^{\lambda}_J(t)$ is the running weighted optimum.
--
--   1. If no job is eligible, every job of $J$ has rate $0$ at $t$ (the algorithm idles).
--   2. Otherwise the eligible job that precedes every other eligible job in $\prec$ has rate $1$, and every other job of $J$ has rate $0$.
--
--   With $\prec$ a strict total order that refines the deadline order, this is the paper's rule: serve the earliest-deadline eligible job, breaking ties by one fixed order.
--
--   **Formalization Note** The tie-breaking order is fixed for the whole run, as in the proof of Theorem 1.2 (Definition 5.4, "under the fixed tie-breaking rule"; Lemma 5.6, "the same strict total order"). The base mission's unweighted run predicate instead lets ties be broken anew at every time. Eligibility requires $t<d_j$, and the threshold uses the running optimum, not the final one.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, p.3 (PDF p.5); Section 5, p.24 (PDF p.26); Definition 5.4, p.25 (PDF p.27); Lemma 5.6, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_pre
import Definitions.Def_MaxMinFracSched_IsSchedule
import Definitions.Def_MaxMinFracSched_work
import Definitions.Def_MaxMinFracSched_Supplement_weightedOptVal

namespace MaxMinFracSched

namespace Supplement

/-- **A WeightedScaledEDF(α′) run with a fixed tie-breaking order.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, p.3 (PDF p.5): "WeightedScaledEDF(α′) then schedules jobs in EDF order,
working on each job i until it has received α′· f̂λJ(t)·wi/λi work"; Section 5, p.24 (PDF p.26):
"serves the earliest-deadline released job i whose completed work ci(t) satisfies ci(t) < θi(t),
where θi(t) := α′ · f̂λ(t) · w̃i … If no released job satisfies the inequality, WeightedScaledEDF
idles"; Definition 5.4, p.25: "under the fixed tie-breaking rule"; Lemma 5.6, p.26: "both runs
prioritize jobs by the same strict total order, namely by deadline with the shared tie-breaking
rule".

Given weights `lam` and a priority relation `prec`, a schedule `r` of `J` is a run when it is
feasible and, for almost every time `t`, with `E t` the set of jobs `j ∈ J` with `a_j ≤ t < d_j` and
`c_j(t) < θ_j(t) = α′ · f̂^λ_J(t) · w_j / λ_j` (`f̂^λ_J(t) = weightedOptVal lam (pre J t)`):
1. if `E t` is empty, every job of `J` has rate `0` at `t`;
2. otherwise the `prec`-first job of `E t` (the one preceding every other job of `E t`) has
   rate `1` and every other job of `J` has rate `0`.

**Formalization Note.** Used with `prec` a strict total order refining the deadline order
(`j.d < k.d → prec j k`), so the `prec`-first eligible job is an eligible job of earliest
deadline, and ties are broken by one fixed order for the whole run (as in the proof of
Theorem 1.2, Definition 5.4 and Lemma 5.6), not anew at every time as in the base
`IsThresholdEDF`. Eligibility requires `t < d_j`. The threshold uses the running weighted
optimum of the jobs released by `t`, never the final value. -/
def IsWeightedScaledEDF (α' : ℝ) (lam : Job → ℝ) (prec : Job → Job → Prop) (J : Finset Job)
    (r : Job → ℝ → ℝ) : Prop :=
  IsSchedule J r ∧
    ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ((J.filter (fun j => j.a ≤ t ∧ t < j.d ∧
          work r j t < α' * weightedOptVal lam (pre J t) * j.w / lam j)) = ∅ →
          ∀ j ∈ J, r j t = 0) ∧
      ((J.filter (fun j => j.a ≤ t ∧ t < j.d ∧
          work r j t < α' * weightedOptVal lam (pre J t) * j.w / lam j)).Nonempty →
          ∃ j ∈ J.filter (fun j => j.a ≤ t ∧ t < j.d ∧
              work r j t < α' * weightedOptVal lam (pre J t) * j.w / lam j),
            (∀ k ∈ J.filter (fun j => j.a ≤ t ∧ t < j.d ∧
                work r j t < α' * weightedOptVal lam (pre J t) * j.w / lam j), k ≠ j → prec j k) ∧
            r j t = 1 ∧ ∀ k ∈ J, k ≠ j → r k t = 0)

end Supplement

end MaxMinFracSched


