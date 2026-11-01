-- Prove2me | Definitions.Def_CompetingAgents_thresholdProcess
-- name    : CompetingAgents_thresholdProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:08.945192+00:00
-- url     : https://prove2.me/theorems/408c154e-8e64-4285-89bb-251456c50582
-- title:
--   The finite-agent stochastic threshold process (4.1)
-- statement:
--   In the finite model, at each time step $t=1,2,\dots$ a fresh cohort of $n$ agents, sampled i.i.d. from $F$, best responds to the criterion $\beta$ and to the previous threshold $\hat S^{t-1}_n$. Let $P^n(\beta,s)$ be the empirical distribution function of the $n$ scores. The thresholds evolve by
--
--   $$\hat S^t_n=q\big(P^n(\beta,\hat S^{t-1}_n)\big),\qquad t=1,2,\dots\tag{4.1}$$
--
--   from a real initial threshold $\hat S^0_n$.
--
--   The cohorts are **fresh**: the agents $A_{t,j}$, over all times $t$ and positions $j$, are independent random variables, each with law $F$.
--
--   This process is the object of the goal theorem: for large $t$ and $n$ it concentrates near the mean-field equilibrium threshold.
--
--   **Formalization Note** Display (4.1) is the definition; the running text of p.9 prints $q(P^{n,t-1})$, a typo for $q(P^{n,t})$. Each cohort reacts to the realized previous threshold, so $\hat S^t_n$ is random through all earlier cohorts. The freshness predicate also asks the unused cohort $t=0$ to be i.i.d. with law $F$, which is harmless.
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, (4.1), p.9; Figure 2 and text, p.10

import Mathlib
import Definitions.Def_CompetingAgents_scoreCDF

open MeasureTheory ProbabilityTheory

namespace CompetingAgents

variable {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι]

/-- `Pⁿ(β, s)`, the empirical distribution function of the scores of a sample `a 0, …, a (n−1)` of
`n` agents who best respond to `β` and the threshold `s` (Sahoo, Wager, *Policy Learning with
Competing Agents*, arXiv:2204.01884v5, §4, p.9). -/
noncomputable def empiricalScoreCDF (M : Model d ι) (β : Cov d) (s : ℝ) {n : ℕ}
    (a : Fin n → ι × Cov d) : ℝ → ℝ :=
  empiricalCDF fun j => score M β s (a j)

/-- The stochastic fixed-point process (4.1) of the finite model (Sahoo, Wager, arXiv:2204.01884v5,
(4.1), p.9): `Ŝⁿ₀ = S0` and `Ŝⁿₜ = q(Pⁿ(β, Ŝⁿ_{t−1}))` for `t = 1, 2, …`, where at time `t` a fresh
cohort `A t 0, …, A t (n−1)` of `n` agents best responds to `β` and to the realized previous
threshold `Ŝⁿ_{t−1}`.

**Formalization Note.** `A t j ω ∈ ι × ℝ^d` is the (type, noise) of agent `j` of cohort `t` on the
outcome `ω`; the cohort `A 0` is never used. Display (4.1) is the definition (the running text of
p.9 prints `q(P^{n,t−1})`, a typo for `q(P^{n,t})`). The initial threshold `S0` is a real number. -/
noncomputable def thresholdProcess (M : Model d ι) (β : Cov d) (n : ℕ) (S0 : ℝ)
    {Ω : Type*} (A : ℕ → Fin n → Ω → ι × Cov d) : ℕ → Ω → ℝ
  | 0 => fun _ => S0
  | t + 1 => fun ω =>
      quantile M.lev (empiricalScoreCDF M β (thresholdProcess M β n S0 A t ω) fun j => A (t + 1) j ω)

/-- The cohorts of the finite model (Sahoo, Wager, arXiv:2204.01884v5, §4, p.9: "at each time step,
`n` new agents with unobservables sampled i.i.d. from `F`"): every `A t j` is a measurable random
agent with law `F`, and the whole family indexed by `(t, j)` is independent. -/
def IsFreshCohorts (M : Model d ι) {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Fin n → Ω → ι × Cov d) : Prop :=
  (∀ t j, Measurable (A t j)) ∧ iIndepFun (fun p : ℕ × Fin n => A p.1 p.2) μ ∧
    ∀ t j, μ.map (A t j) = agentLaw M

end CompetingAgents


