-- Prove2me | Definitions.Def_QueueBandit_EarlyLower_Model
-- name    : QueueBandit_EarlyLower_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:37.01699+00:00
-- url     : https://prove2.me/theorems/7f3b812a-8149-45c4-9dce-2f615928090f
-- title:
--   §3.2, pp. 7–8 — load gaps ε_u (Assumption 2) and the stationary initial law π_(λ,μ*) of the genie queues (Assumption 3)
-- statement:
--   This file adds Assumptions 2 and 3 of Krishnasamy, Sen, Johari and Shakkottai (§3.2) to the shared model of the $U\times K$ switch: the queues $Q$ and the genie queues $Q^*$, the counts $T_{uk}(t+1)$, the queue-regret $\Psi_u(t)=\mathbb E[Q_u(t)-Q^*_u(t)]$, Assumption 1, $\Delta$, $D(\mu)$ and $\alpha$-consistency.
--
--   Queue $u$ receives an arrival in each slot with probability $\lambda_u$, and $k^*_u$ is its optimal server, with $\mu^*_u=\mu_{uk^*_u}$. The **load gap** of queue $u$ is
--
--   $$\epsilon_u=\mu^*_u-\lambda_u ,$$
--
--   and **Assumption 2** (stability) asks $\epsilon_u>0$ for every $u$.
--
--   **Assumption 3** asks that the initial state $Q(0)$ be distributed according to the stationary law $\pi_{(\lambda,\mu^*)}$ of $Q^*$. The genie queue $Q^*_u$ is a birth–death chain that moves up with probability $\lambda_u(1-\mu^*_u)$ and down with probability $(1-\lambda_u)\mu^*_u$, so its stationary law is geometric,
--
--   $$P(Q_u(0)=n)=(1-\rho_u)\rho_u^n,\qquad \rho_u=\frac{\lambda_u(1-\mu^*_u)}{(1-\lambda_u)\mu^*_u},$$
--
--   and $\pi_{(\lambda,\mu^*)}$ is the product of these laws over the queues (the genie queues are driven by independent arrivals and services).
--
--   These objects enter Lemma 22 and Theorem 8.
--
--   **Formalization Note.** Queues are indexed by `Fin U` and servers by `Fin K` (0-based). The switch, the policies, the seed space, the queues, the counts and the queue-regret are the shared definitions `QueueBandit.LateLower.Dynamics` and `QueueBandit.LateLower.Instance`. In `initLaw` the success parameter $1-\rho_u$ is clamped to $[0,1]$; under Assumption 2 it already lies in $(0,1]$, so the clamp does nothing. The geometric law is the stationary law of the printed recursion (arrivals and services in the same slot). The paper's tail formula on p. 30 belongs to a service-before-arrival convention.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, pp. 7–8 (§3.2, notation, Assumptions 2–3)

import Mathlib
import Definitions.Def_QueueBandit_LateLower_Dynamics
import Definitions.Def_QueueBandit_LateLower_Instance

open MeasureTheory ProbabilityTheory

namespace QueueBandit.EarlyLower

/-! # Assumptions 2 and 3 of Krishnasamy, Sen, Johari and Shakkottai (arXiv:1604.06377v4, §3.2)

The switch itself (matchings, policies, the seed space, the queues `Q` and `Q*`, the counts
`T_uk(t + 1)`, their expectations, the queue-regret `Ψ_u(t)`, Assumption 1, `Δ`, `D(μ)` and
α-consistency) is the shared model `QueueBandit.LateLower`. This file adds the load gaps `ε_u`
(Assumption 2) and the stationary initial law `π_{(λ, μ*)}` (Assumption 3). Queues are `Fin U`,
servers `Fin K` (0-based indices for the paper's `[U]`, `[K]`). -/

/-- `μ*_u = μ_{u k*_u}`, the best service probability of queue `u` (p. 7). -/
def muStarU {U K : ℕ} (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) (u : Fin U) : ℝ :=
  mu u (kstar u)

/-- `ε_u = μ*_u − λ_u`, the load gap of queue `u` (p. 7); Assumption 2 is `ε_u > 0` for all `u`. -/
def eps {U K : ℕ} (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (u : Fin U) : ℝ :=
  muStarU mu kstar u - lam u

/-- `ρ_u = λ_u(1 − μ*_u) / ((1 − λ_u) μ*_u)`, the ratio of the up and down probabilities of the
genie queue `Q*_u` (a birth–death chain). -/
noncomputable def rho {U K : ℕ} (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (u : Fin U) : ℝ :=
  lam u * (1 - muStarU mu kstar u) / ((1 - lam u) * muStarU mu kstar u)

/-- Assumption 3 (p. 8): the stationary law `π_{(λ, μ*)}` of `Q*`, the product over queues of the
geometric laws `P(Q_u(0) = n) = (1 − ρ_u) ρ_u^n` (Mathlib's `geometricMeasure p` puts mass
`(1 − p)^n p` on `n`). Under Assumption 2, `ρ_u ∈ [0, 1)`, so the clamp `projIcc` to `[0, 1]` is
the identity. -/
noncomputable def initLaw {U K : ℕ} (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ)
    (kstar : Fin U → Fin K) : Measure (Fin U → ℕ) :=
  Measure.pi (fun u => geometricMeasure (Set.projIcc 0 1 zero_le_one (1 - rho lam mu kstar u)))

end QueueBandit.EarlyLower


