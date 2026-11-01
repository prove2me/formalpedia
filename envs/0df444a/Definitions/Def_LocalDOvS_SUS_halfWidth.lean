-- Prove2me | Definitions.Def_LocalDOvS_SUS_halfWidth
-- name    : LocalDOvS_SUS_halfWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:11.391536+00:00
-- url     : https://prove2.me/theorems/75ca5b37-034a-4042-8afb-04086046c822
-- title:
--   Confidence half-width $h(n,\sigma,\alpha)$
-- statement:
--   The **confidence half-width**
--
--   $$
--   h(n,\sigma,\alpha):=\sqrt{\frac{2\sigma^2}{n}\log\frac2\alpha}.
--   $$
--
--   By Hoeffding's inequality for sub-Gaussian outputs, $[\hat F_n(x)-h(n,\sigma,\alpha),\hat F_n(x)+h(n,\sigma,\alpha)]$ is a $(1-\alpha)$ confidence interval for $f(x)$ from $n$ independent simulations.
--
--   **Formalization Note** At $n=0$ the formula divides by zero and returns $0$; the algorithm only uses $n\ge1$.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §3.1, p.13

import Mathlib

open scoped NNReal

namespace LocalDOvS.SUS

/-- The confidence half-width `h(n, σ, α) := √(2σ²/n · log(2/α))` (Zhang–Zheng–Lavaei,
arXiv:2012.02427v2, §3.1, p.13), which makes `[F̂_n(x) − h, F̂_n(x) + h]` a `(1 − α)` confidence
interval for `f(x)` from `n` independent simulations by Hoeffding's inequality.

**Formalization Note.** At `n = 0` the formula divides by zero and Lean returns `0`; the
algorithm of this mission only evaluates it at sample sizes `n ≥ 1`. -/
noncomputable def halfWidth (σ : ℝ≥0) (α : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * (σ : ℝ) ^ 2 / n * Real.log (2 / α))

end LocalDOvS.SUS


