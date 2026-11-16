-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_weightedOptVal
-- name    : MaxMinFracSched_Supplement_weightedOptVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:11:08.912936+00:00
-- url     : https://prove2.me/theorems/5e762434-4f9c-402d-8bec-e29bf32ff899
-- title:
--   Weighted offline optimum $\hat f^{\lambda}_J$ (uncapped)
-- statement:
--   Let $J$ be an instance and let $\lambda$ assign a weight $\lambda_j$ to every job. A schedule that completes $c_j\le w_j$ units of work on job $j$ by its deadline gives that job the **value** $\lambda_j c_j/w_j=\lambda_j f_j$. The **weighted offline optimum** is
--   $$
--   \hat f^{\lambda}_J=\sup\Bigl\{v\ge 0:\ \text{some feasible schedule } r \text{ of } J \text{ has } \lambda_j f_j(r)\ge v \text{ for every } j\in J\Bigr\}.
--   $$
--   The **running weighted optimum** at time $t$ is $\hat f^{\lambda}_J(t)=\hat f^{\lambda}_{J_{\le t}}$, the weighted optimum of the jobs released by time $t$.
--
--   This is the benchmark of the weighted max-min problem (Section 1 and Section 5). Unlike the unweighted optimum it is not capped at $1$: a single job with weight $\Lambda>1$ and a window as long as its work has $\hat f^{\lambda}=\Lambda$ (p.25).
--
--   **Formalization Note** The supremum is taken over feasible rate schedules, not computed by the formula $\min(\lambda_{\min},\hat g)$ of Lemma 5.1. For a valid nonempty instance with positive weights the set contains $0$ and is bounded by $\min_j\lambda_j$. For the empty instance Lean's real supremum of an unbounded set is $0$; the running optimum is only used at times when some job has arrived.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3); Section 5, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_IsSchedule
import Definitions.Def_MaxMinFracSched_work
import Definitions.Def_MaxMinFracSched_frac

namespace MaxMinFracSched

namespace Supplement

/-- **The weighted offline optimum `f̂^λ_J`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3): "In the weighted setting, each job i has a positive weight λi,
revealed online along with the rest of the job, and a schedule that completes ci work on job i
receives value λici/wi from that job. The objective is to maximize the minimum value over all
jobs"; Section 5, p.23 (PDF p.25): "let f̂λJ(t) denote the optimal weighted objective value on the
prefix instance J≤t".

`weightedOptVal lam J` is the supremum of the values `v ≥ 0` such that some feasible schedule
`r` of `J` gives every job `j ∈ J` value `lam j · frac r j ≥ v` (`frac` caps the work at `w_j`, so
`lam j · frac r j = λ_j c_j / w_j` with `c_j ≤ w_j`).

**Formalization Note.** The value is **not** capped at `1` (a single job with `λ = Λ > 1` and a
long enough window has `f̂^λ = Λ`, p.25). It is defined over feasible schedules, not by the formula
`min(λ_min, ĝ)` of Lemma 5.1. For a nonempty instance of valid jobs with positive weights the set
contains `0` and is bounded by `min_j λ_j`; for `J = ∅` it is unbounded and the real `sSup` is
`0` (never used: the running optimum is only evaluated at times with a released job). The running
optimum `f̂^λ_J(t)` is `weightedOptVal lam (pre J t)`. -/
noncomputable def weightedOptVal (lam : Job → ℝ) (J : Finset Job) : ℝ :=
  sSup {v : ℝ | 0 ≤ v ∧ ∃ r, IsSchedule J r ∧ ∀ j ∈ J, v ≤ lam j * frac r j}

end Supplement

end MaxMinFracSched


