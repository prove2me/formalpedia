-- Prove2me | Definitions.Def_NumStochOpt_ListScheduling_Makespan
-- name    : NumStochOpt_ListScheduling_Makespan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T20:49:11.055501+00:00
-- url     : https://prove2.me/theorems/77b03344-6f41-421e-9f12-e533617fa80b
-- title:
--   Machine loads, makespan, the minimum makespan $C^*_n(m)$ and $p_{\max}$
-- statement:
--   This file fixes the second-stage problem of the machine investment problem: scheduling $n$ jobs on $m$ identical machines so as to minimize the makespan.
--
--   Let $p_1, p_2, \dots$ be nonnegative processing times; an instance with $n$ jobs uses the first $n$ of them. Jobs are processed without interruption, each machine processes one job at a time, and there are no precedence constraints, so a schedule is determined, up to idle time, by an **assignment** $\sigma : \{1,\dots,n\} \to \{1,\dots,m\}$ of jobs to machines. The **load** of machine $i$ is $\sum_{j : \sigma(j) = i} p_j$, and the **makespan** of $\sigma$ is the largest load,
--
--   $$
--   C(\sigma) = \max_{i = 1,\dots,m} \sum_{j:\ \sigma(j) = i} p_j ,
--   $$
--
--   "the maximum sum of the processing times assigned to any one machine". The **minimum makespan** is
--
--   $$
--   C^*_n(m) = \min_{\sigma} C(\sigma),
--   $$
--
--   the minimum over all $m^n$ assignments. The file also defines $p_{\max} = \max_{j=1,\dots,n} p_j$.
--
--   These are the objects of every result in the mission: $C^*_n(m)$ is the second-stage optimal value in the two-stage cost $Z_n(m) = cm + \mathbb E\, C^*_n(m)$ of (8.9).
--
--   **Formalization Note** Processing times are a sequence `p : ℕ → ℝ`, 0-based: the book's job $j$ is `p (j-1)`, and the $n$-job instance uses `p 0, …, p (n-1)`. Machines are `Fin m`. Maxima and minima over the finite nonempty index types are `⨆`/`⨅`, which are attained. With $m = 0$ machines and $n \ge 1$ jobs there is no assignment and `optMakespan n 0 p = 0` by the convention for an empty infimum; every theorem assumes $m \ge 1$. For $n = 0$, `maxProcTime 0 p = 0`.
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, p. 205, definition of the makespan and C*_n(m) (with Eq. (8.9)); p. 206, p_max

import Mathlib

namespace NumStochOpt.ListScheduling

/-- The load of machine `i` under the assignment `σ` of the first `n` jobs to `m` identical
machines: the sum of the processing times `p j` of the jobs `j < n` with `σ j = i`.
Job `j` (0-based) is the book's job `j + 1`. -/
def machineLoad {n m : ℕ} (p : ℕ → ℝ) (σ : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j : Fin n, if σ j = i then p (j : ℕ) else 0

/-- The makespan of the assignment `σ`: the maximum load of any one machine
(Rinnooy Kan–Stougie, Ch. 8 of Ermoliev & Wets (1988), p. 205). -/
noncomputable def makespan {n m : ℕ} (p : ℕ → ℝ) (σ : Fin n → Fin m) : ℝ :=
  ⨆ i : Fin m, machineLoad p σ i

/-- The minimum makespan `C*_n(m)` of the first `n` jobs (processing times `p 0, …, p (n-1)`)
on `m` identical machines: the minimum over all assignments `σ : Fin n → Fin m` of the
makespan. Only meaningful for `m ≥ 1`; every theorem assumes it. -/
noncomputable def optMakespan (n m : ℕ) (p : ℕ → ℝ) : ℝ :=
  ⨅ σ : Fin n → Fin m, makespan p σ

/-- `p_max = max_{j = 1, …, n} p_j`, the largest of the first `n` processing times
(`0` when `n = 0`). -/
noncomputable def maxProcTime (n : ℕ) (p : ℕ → ℝ) : ℝ :=
  ⨆ j : Fin n, p (j : ℕ)

end NumStochOpt.ListScheduling


