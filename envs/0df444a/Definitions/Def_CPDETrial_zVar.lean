-- Prove2me | Definitions.Def_CPDETrial_zVar
-- name    : CPDETrial_zVar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:48:58.315657+00:00
-- url     : https://prove2.me/theorems/dfae9139-ef46-406e-b3c1-f2e2ad207eec
-- title:
--   Predictive variance $\sigma^2_{Z^\tau_i}$ (eq. (10))
-- statement:
--   For $l=\lambda_i$, $s=\Sigma^t_{i,i}$ and $\tau\in\mathbb N$,
--
--   $$
--   \sigma^2_{Z^\tau_i}=\frac{s^2\tau}{l+\tau s}=\frac{\lambda_i\tau}{n^t_i(n^t_i+\tau)},\qquad n^t_i=\lambda_i/\Sigma^t_{i,i},
--   $$
--
--   the variance of the change in the mean belief about arm $i$ after $\tau$ observations of arm $i$.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 10, eq. (10)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The variance `σ²_{Z^τ_i}` of eq. (10).**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §3.1, eq. (10), p. 10: "`σ²_{Z^τ_i} = λ_i τ/(n^t_i(n^t_i + τ))`" with `n^t_i = λ_i/Σ^t_{i,i}`.

`zVar l s τ = s² τ/(l + τ s)` for `l = λ_i`, `s = Σ^t_{i,i}`, which equals `λ_i τ/(n_i(n_i + τ))`
when `s > 0`.

**Formalization Note.** Stored as `ℝ≥0` (the type of `gaussianReal`'s variance) via
`Real.toNNReal`; the value is nonnegative for `l > 0`, `s ≥ 0`, so the truncation never acts. -/
noncomputable def zVar (l : ℝ≥0) (s : ℝ) (τ : ℕ) : ℝ≥0 :=
  Real.toNNReal (s ^ 2 * (τ : ℝ) / ((l : ℝ) + (τ : ℝ) * s))

end CPDETrial


