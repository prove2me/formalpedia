-- Prove2me | Definitions.Def_CPDETrial_zProc
-- name    : CPDETrial_zProc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:47:35.264093+00:00
-- url     : https://prove2.me/theorems/ae349339-74ce-4b72-8f2d-1d0985c21064
-- title:
--   Predictive process $Z^\tau_i$ of the lookahead
-- statement:
--   For $l=\lambda_i>0$ and $s=\Sigma^t_{i,i}$, the change $Z^\tau_i=\mu^{t+\tau}_i-\mu^t_i$ of the mean belief about arm $i$ after $\tau$ further observations of arm $i$ is realized on the canonical space as
--
--   $$
--   Z^\tau(\omega) = \frac{s\left(\tau\sqrt{s}\,\omega_0 + \sqrt{l}\sum_{r=1}^{\tau}\omega_r\right)}{l+\tau s}.
--   $$
--
--   This is eq. (8) applied to observations $Y^{t+r}_i-\mu^t_i=\sqrt{s}\,\omega_0+\sqrt{l}\,\omega_r$. Then $Z^0=0$ and $Z^\tau\sim N(0,\sigma^2_{Z^\tau_i})$ with $\sigma^2_{Z^\tau_i}=s^2\tau/(l+\tau s)=\lambda_i\tau/(n_i(n_i+\tau))$, $n_i=\lambda_i/\Sigma^t_{i,i}$, as in eq. (10).
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 10, eqs. (9)–(10)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The predictive process `Z^τ_i` of eqs. (9)–(10).**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §3.2, p. 10: "`Z^τ_i ≡ µ^{t+τ}_i − µ^t_i`", with
"`Z^τ_i ∼ N(0, σ²_{Z^τ_i})` where `σ²_{Z^τ_i} = λ_i τ/(n^t_i(n^t_i + τ))`", `n^t_i = λ_i/Σ^t_{i,i}`.

For `l = λ_i`, `s = Σ^t_{i,i}` and `ω` a point of the canonical space (`idxP`),
`zProc l s τ ω = s (τ √s ω₀ + √l Σ_{r=1}^{τ} ω_r)/(l + τ s)`.
This is (8) applied to `τ` observations `Y^{t+r}_i − µ^t_i = √s ω₀ + √l ω_r` of arm `i` (prior
uncertainty plus noise): `Z^0 = 0`, and under `idxP` the variable `Z^τ` is centred normal with
variance `s² τ/(l + τ s) = λ_i τ/(n_i(n_i + τ))`, as in (10).

**Formalization Note.** The process is realized on one canonical space for every `(λ_i, Σ^t_{i,i})`;
only its law enters the index. The denominator is positive for `l > 0`, `s ≥ 0`. -/
noncomputable def zProc (l : ℝ≥0) (s : ℝ) (τ : ℕ) (ω : ℕ → ℝ) : ℝ :=
  s * ((τ : ℝ) * Real.sqrt s * ω 0 + Real.sqrt (l : ℝ) * ∑ r ∈ Finset.Icc 1 τ, ω r) /
    ((l : ℝ) + (τ : ℝ) * s)

end CPDETrial


