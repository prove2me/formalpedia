-- Prove2me | Definitions.Def_ManIAL_dualStep
-- name    : ManIAL_dualStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:01.402346+00:00
-- url     : https://prove2.me/theorems/b8bd44c1-6f27-4cf1-bb34-34034c422639
-- title:
--   Dual step size (3.13)
-- statement:
--   Algorithm 1 updates the multiplier with the step size
--
--   $$
--   \beta_{k+1}=\beta_0\min\left(\frac{\|\mathcal Ax^0-y^0\|\log^2 2}{\|\mathcal Ax^{k+1}-y^{k+1}\|(k+1)^2\log(k+2)},\,1\right),
--   $$
--
--   where $\beta_0>0$ is the initial dual step size. The choice makes $\sum_l\beta_l\|\mathcal Ax^l-y^l\|$ summable, which keeps the multipliers bounded (display (3.31)).
--
--   **Formalization Note** $\log$ is the natural logarithm. When $\mathcal Ax^{k+1}=y^{k+1}$ the quotient is a division by zero, which Lean evaluates to $0$ (so $\beta_{k+1}=0$ instead of $\beta_0$); since $\beta_{k+1}$ only enters through $\beta_{k+1}(\mathcal Ax^{k+1}-y^{k+1})=0$, the iterates are unchanged.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Algorithm 1, step 6, display (3.13), p.9

import Mathlib

namespace ManIAL

/-- The dual step size (3.13) of Algorithm 1 (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.9):
`β_{k+1} = β₀ · min(‖Ax⁰ − y⁰‖ log² 2 / (‖Ax^{k+1} − y^{k+1}‖ (k + 1)² log(k + 2)), 1)`,
with `x = x^{k+1}`, `y = y^{k+1}`.

**Formalization Note.** `log` is the natural logarithm `Real.log`. If `Ax^{k+1} = y^{k+1}`, Lean's
`a / 0 = 0` gives `β_{k+1} = 0` where the formula gives `β₀`; `β_{k+1}` only enters Algorithm 1
through `β_{k+1}(Ax^{k+1} − y^{k+1}) = 0`, so the iterates are the same. -/
noncomputable def dualStep {n m : ℕ} (β₀ : ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n)) (y₀ : EuclideanSpace ℝ (Fin m)) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  β₀ * min (‖A x₀ - y₀‖ * Real.log 2 ^ 2 /
    (‖A x - y‖ * ((k : ℝ) + 1) ^ 2 * Real.log ((k : ℝ) + 2))) 1

end ManIAL


