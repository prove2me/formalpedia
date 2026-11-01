-- Prove2me | Definitions.Def_CompetingAgents_noiseCDF
-- name    : CompetingAgents_noiseCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:42.610016+00:00
-- url     : https://prove2.me/theorems/c0d5df33-6136-40ad-9519-dfb75fa188bc
-- title:
--   Noise distributions: $\Phi_\sigma$, $\varphi_\sigma$ and $N(0,\sigma^2 I_d)$
-- statement:
--   $\Phi_\sigma$ is the distribution function of the normal law $N(0,\sigma^2)$ with mean $0$ and variance $\sigma^2$, and $\varphi_\sigma$ is its density
--
--   $$\varphi_\sigma(u)=\frac{1}{\sqrt{2\pi\sigma^2}}\,e^{-u^2/(2\sigma^2)}.$$
--
--   The noise $\epsilon$ added to an agent's covariates has the multivariate normal law $N(0,\sigma^2 I_d)$ on $\mathbb R^d$.
--
--   $\Phi_\sigma$ enters the expected utility (2.2), and $\varphi_\sigma'$ the derivative formula (E.1).
--
--   **Formalization Note** Mathlib's `gaussianReal 0 v` is parametrised by the variance $v=\sigma^2$. The multivariate law is `multivariateGaussian 0 (σ² • 1)`.
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, (2.2), p.6; Lemma 28, p.31; $\epsilon_i\sim N(0,\sigma^2\mathbf I_d)$, p.6

import Mathlib
import Definitions.Def_CompetingAgents_Model

open MeasureTheory ProbabilityTheory

namespace CompetingAgents

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- `Φ_σ`, the distribution function of the normal law `N(0, σ²)` with mean `0` and variance `σ²`
(Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, p.6, below (2.2)).

**Formalization Note.** `gaussianReal 0 v` is parametrised by its variance `v = σ²`, not by `σ`. -/
noncomputable def noiseCDF (M : Model d ι) (r : ℝ) : ℝ :=
  cdf (gaussianReal 0 (Real.toNNReal (M.σ ^ 2))) r

/-- `φ_σ`, the density of `N(0, σ²)` (Sahoo, Wager, arXiv:2204.01884v5, Lemma 28, p.31: "the Normal
p.d.f. with mean 0 and variance σ²"). -/
noncomputable def noiseDensity (M : Model d ι) (r : ℝ) : ℝ :=
  gaussianPDFReal 0 (Real.toNNReal (M.σ ^ 2)) r

/-- The law `N(0, σ² I_d)` of the noise `εᵢ` on `ℝ^d` (Sahoo, Wager, arXiv:2204.01884v5, p.6). It is
the multivariate Gaussian with mean `0` and covariance matrix `σ² I_d`. -/
noncomputable def noiseLaw (M : Model d ι) : Measure (Cov d) :=
  multivariateGaussian 0 ((M.σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))

end CompetingAgents


