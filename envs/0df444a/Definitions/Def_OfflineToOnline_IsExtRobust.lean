-- Prove2me | Definitions.Def_OfflineToOnline_IsExtRobust
-- name    : OfflineToOnline_IsExtRobust
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:23.235194+00:00
-- url     : https://prove2.me/theorems/0544a00c-68fb-4df8-9952-eb0ec6f52694
-- title:
--   Extended $(\gamma,\delta)$-robust approximation
-- statement:
--   An instance of Algorithm 1 is an **extended $(\gamma,\delta)$-robust approximation** if the following holds for every horizon $T\ge1$, every $f_1,\dots,f_T\in\mathcal F$ and every $h=h(T)\ge0$. Let $\tilde\theta$ be a noisy policy whose parameters satisfy, for every subproblem $i\in[N]$ and every coordinate $j\in[d_{\mathrm{payoff}}]$,
--
--   $$
--   \Big[\sum_{t=1}^T\textsc{Payoff}\big(\tilde\theta_t^{(i)},z_t^{(i-1)},f_t\big)\Big]_j+h\ \ge\ 0
--   $$
--
--   on every realization of the seeds, where $z_t^{(i)}$ are the points of the runs under $\tilde\theta$. Then
--
--   $$
--   \sum_{t=1}^T\mathbb E\big[f_t(z_t)\big]\ \ge\ \gamma\sum_{t=1}^T f_t(\hat z)-\delta N h\qquad\text{for every }\hat z\in\mathcal C .
--   $$
--
--   The definition asks the greedy algorithm to degrade gracefully when its local optimality conditions are met only on average over $T$ runs, with an additive error proportional to the total slack $h$.
--
--   **Formalization Note** The function $h(\cdot):\mathbb N\to\mathbb R_+$ of the paper enters only through $h(T)$, so it is a real $h\ge0$ for each $T$. The slack condition is required on every seed realization. The ranges $\gamma\in(0,1)$, $\delta>0$ are hypotheses of the theorems that use the definition.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Definition 6, p.16

import Mathlib
import Definitions.Def_OfflineToOnline_IGInstance
import Definitions.Def_OfflineToOnline_runPoints
import Definitions.Def_OfflineToOnline_seedLaw
import Definitions.Def_OfflineToOnline_IsNoisyPolicy

namespace OfflineToOnline

/-- Extended `(γ, δ)`-robust approximation, Definition 6, p.16. For every `T ≥ 1`, every
`f_1, …, f_T ∈ F` and every `h(T) = h ≥ 0`: whenever a noisy adapted policy `θ̃` satisfies, for
every subproblem `i` and coordinate `j`,
`[∑_{t=1}^T Payoff(θ̃_t^(i), z_t^(i−1), f_t)]_j + h ≥ 0`, the runs satisfy
`∑_{t=1}^T E[f_t(z_t)] ≥ γ ∑_{t=1}^T f_t(ẑ) − δ N h` for every `ẑ ∈ C` (`zhat` in Lean).

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Definition 6, p.16.

Formalization Note: the condition on the noisy parameters is required for every seed
realization `ω` (they are random through `z_t^(i−1)`). `h(·) : ℕ → ℝ₊` enters only through `h(T)`,
so it is a real `h ≥ 0` per `T`. The expectation is over the product law `seedLaw ν T N` of the
seeds. The restrictions `γ ∈ (0, 1)`, `δ > 0` are hypotheses of the theorems that use the
definition. Runs and subproblems are `0`-indexed. -/
def IsExtRobust {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω] {m d : ℕ}
    (I : IGInstance D Ω m d) (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
    (γ δ : ℝ) : Prop :=
  ∀ T : ℕ, 1 ≤ T → ∀ f : Fin T → D → ℝ, (∀ t, f t ∈ I.F) → ∀ h : ℝ, 0 ≤ h →
    ∀ θ : Fin T → Fin I.N → (Fin T → Fin I.N → Ω) → Fin m → ℝ, IsNoisyPolicy I T θ →
      (∀ (ω : Fin T → Fin I.N → Ω) (i : Fin I.N) (j : Fin d),
          0 ≤ (∑ t, I.payoff (θ t i ω) (runPoints I θ t i ω) (f t)) j + h) →
      ∀ zhat ∈ I.C, γ * ∑ t, f t zhat - δ * I.N * h ≤
        ∑ t, ∫ ω, f t (runPoints I θ t I.N ω) ∂(seedLaw ν T I.N)

end OfflineToOnline


