-- Prove2me | Definitions.Def_ConvBoundsQA_tailDist
-- name    : ConvBoundsQA_tailDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:17.37068+00:00
-- url     : https://prove2.me/theorems/2bcbdef1-6824-45e9-9f1f-df511456ffbd
-- title:
--   The $t$-tail distribution $\mu^{t+}$
-- statement:
--   For $\mu\in\mathcal M$ and $t\in[0,1)$, the **$t$-tail distribution** $\mu^{t+}$ is the probability measure with
--   $$
--   \mu^{t+}(-\infty,x]=\max\Bigl\{\frac{\mu(-\infty,x]-t}{1-t},\,0\Bigr\},\qquad x\in\mathbb R,
--   $$
--   the law of $q_U(\mu)$ for $U$ uniform on $[t,1]$, i.e. $\mu$ restricted beyond its $t$-quantile. A distribution "admits a decreasing density beyond its $t$-quantile" when $\mu^{t+}$ admits a decreasing density. For a tuple, $\mu^{t+}=(\mu_1^{t+},\dots,\mu_n^{t+})$.
--
--   **Formalization Note** $\mu^{t+}$ is the Stieltjes measure of the distribution function $x\mapsto\max(F_\mu(x)-t,0)/\max(1-t,0)$, which equals the displayed formula for $t<1$; for $t\in[0,1)$ it is a probability measure and $\mu^{0+}=\mu$.
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, §4, p.10

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ConvBoundsQA

/-- The distribution function of the `t`-tail distribution:
`x ↦ max {(μ(−∞, x] − t)/(1 − t), 0}` (Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §4, p.10).

**Formalization Note** It is written `max (F(x) − t) 0 / max (1 − t) 0` with `F = cdf μ`, which is
the page's formula for `t < 1` (the only range used) and makes the function monotone for every `t`.
For a probability measure `cdf μ x = μ(−∞, x]`. -/
noncomputable def tailCdf (μ : Measure ℝ) (t : ℝ) : StieltjesFunction ℝ where
  toFun x := max (cdf μ x - t) 0 / max (1 - t) 0
  mono' := by
    intro x y hxy
    exact div_le_div_of_nonneg_right
      (max_le_max (sub_le_sub_right ((cdf μ).mono hxy) t) le_rfl) (le_max_right _ _)
  right_continuous' := by
    intro x
    have hφ : Continuous (fun y : ℝ => max (y - t) 0 / max (1 - t) 0) := by fun_prop
    exact hφ.continuousAt.comp_continuousWithinAt ((cdf μ).right_continuous x)

/-- The `t`-tail distribution `μ^{t+}` of `μ`, for `t ∈ [0, 1)`: the probability measure with
`μ^{t+}(−∞, x] = max {(μ(−∞, x] − t)/(1 − t), 0}`, the law of `q_U(μ)` with `U` uniform on `[t, 1]`
(Blanchet, Lam, Liu, Wang, arXiv:2007.09320v5, §4, p.10). "`μ` admits a decreasing density beyond
its `t`-quantile" means that `μ^{t+}` admits a decreasing density (p.10).

**Formalization Note** It is the Stieltjes measure of `tailCdf μ t`, i.e. the unique measure with that
distribution function. -/
noncomputable def tailDist (μ : Measure ℝ) (t : ℝ) : Measure ℝ :=
  (tailCdf μ t).measure

end ConvBoundsQA


