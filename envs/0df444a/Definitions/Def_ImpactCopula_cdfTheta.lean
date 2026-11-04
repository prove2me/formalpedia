-- Prove2me | Definitions.Def_ImpactCopula_cdfTheta
-- name    : ImpactCopula_cdfTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:11.821243+00:00
-- url     : https://prove2.me/theorems/ea3d7d8f-940f-42da-8310-d40ebab496ff
-- title:
--   Marginal distribution function $F_\theta$ of the residual return
-- statement:
--   Let $\mu$ be the joint law of $(X_i, \theta_i)$ on $\mathbb R^2$. The **marginal distribution function** of the residual return is
--
--   $$
--   F_\theta(y) = \mathbb P(\theta_i \le y) = \mu\big(\mathbb R \times (-\infty, y]\big), \qquad y \in \mathbb R .
--   $$
--
--   **Formalization Note** $F_\theta$ is the published distribution function of the second marginal `μ.map Prod.snd`.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), §3.1, eq. (10), p.10 (PDF p.13)

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

open MeasureTheory

namespace ImpactCopula

/-- The marginal distribution function `F_θ` of the residual return (§2.1 and (10)), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024),
p.10 (PDF p.13): `F_θ(y) = ℙ(θ_i ≤ y)`, where `(X_i, θ_i) ∼ F` and `F` is the law `μ` on `ℝ²`.

**Formalization Note.** `F_θ` is the published distribution function of the second marginal
`μ.map Prod.snd`. -/
noncomputable def cdfTheta (μ : Measure (ℝ × ℝ)) : ℝ → ℝ :=
  RiskFunctionals.StochDominance.distributionFunction (μ.map Prod.snd)

end ImpactCopula


