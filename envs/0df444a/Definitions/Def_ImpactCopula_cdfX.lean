-- Prove2me | Definitions.Def_ImpactCopula_cdfX
-- name    : ImpactCopula_cdfX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:08.567106+00:00
-- url     : https://prove2.me/theorems/fb590851-84ce-490c-9359-25cb6d6da573
-- title:
--   Marginal distribution function $F_X$ of the impact factor
-- statement:
--   Let $F$ be the joint law of a pair $(X_i, \theta_i)$ of an impact factor and a residual return, a probability measure $\mu$ on $\mathbb R^2$. The **marginal distribution function** of the impact factor is
--
--   $$
--   F_X(x) = \mathbb P(X_i \le x) = \mu\big((-\infty, x] \times \mathbb R\big), \qquad x \in \mathbb R .
--   $$
--
--   It is non-decreasing and right-continuous; its discontinuity points $\Delta_X$ are the atoms of $X_i$, at most countably many.
--
--   **Formalization Note** $F_X$ is the published distribution function `RiskFunctionals.StochDominance.distributionFunction` of the first marginal `μ.map Prod.fst`.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), §3.1, eq. (10), p.10 (PDF p.13)

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

open MeasureTheory

namespace ImpactCopula

/-- The marginal distribution function `F_X` of the impact factor (§2.1 and (10)), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024),
p.10 (PDF p.13): `F_X(x) = ℙ(X_i ≤ x)`, where `(X_i, θ_i) ∼ F` and `F` is the law `μ` on `ℝ²`.

**Formalization Note.** The joint law `F` of Assumption (A1) is a measure `μ` on `ℝ × ℝ` (a
probability measure in every statement), and `F_X` is the published distribution function of the
first marginal `μ.map Prod.fst`. -/
noncomputable def cdfX (μ : Measure (ℝ × ℝ)) : ℝ → ℝ :=
  RiskFunctionals.StochDominance.distributionFunction (μ.map Prod.fst)

end ImpactCopula


