-- Prove2me | Definitions.Def_DDROFB_bwdDev
-- name    : DDROFB_bwdDev
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:03:57.195702+00:00
-- url     : https://prove2.me/theorems/48efdcd0-cf62-44c0-afc3-bbbdefd4f989
-- title:
--   Backward deviation $\sigma_b(\mathbb P_i)$ of a univariate law
-- statement:
--   Let $\mathbb Q$ be a probability measure on $\mathbb R$ with mean $\mu = \mathbb E^{\mathbb Q}[\tilde z]$. Its **backward deviation** is
--
--   $$
--   \sigma_b(\mathbb Q) \;=\; \sup_{x>0} \sqrt{\frac{2\mu}{x} + \frac{2}{x^2}\log\mathbb E^{\mathbb Q}\bigl[e^{-x\tilde z}\bigr]} \;\in [0,\infty].
--   $$
--
--   It is the forward deviation of $-\tilde z$ and controls the left tail: $\log\mathbb E[e^{-x(\tilde z-\mu)}] \le x^2\sigma_b(\mathbb Q)^2/2$ for every $x>0$.
--
--   **Formalization Note** As for the forward deviation: the value is an extended nonnegative real, $+\infty$ when the mean does not exist, and the term for an $x>0$ with $\mathbb E[e^{-x\tilde z}] = \infty$ is $+\infty$, so Lean's default values never produce a small finite deviation.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (20), p. 18

import Mathlib
open MeasureTheory Classical
open scoped ENNReal

namespace DDROFB

/-- **Backward deviation** `σ_b(P_i)` of a univariate law, eq. (20).
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (20), p. 18:
"`σ_bi(P_i) = sup_{x>0} √(2μ_i/x + (2/x²) log(E^{P_i}[e^{−x ũ_i}]))`, where `E^{P_i}[ũ_i] = μ_i`."

`bwdDev Q` is the supremum over `x > 0` of `√(2μ/x + (2/x²) log ∫ e^{−xz} dQ(z))`, with
`μ = ∫ z dQ(z)`, as an extended nonnegative real.

**Formalization Note.** As for `fwdDev`: values in `ℝ≥0∞`, `⊤` when the mean does not exist and
`⊤` for an `x > 0` at which `E[e^{−xz}]` is infinite, so Lean's default values `∫ = 0`,
`log 0 = 0` never produce a small finite deviation for a heavy left tail. For a probability
measure the radicand is `≥ 0` by Jensen's inequality (`log E[e^{−xz}] ≥ −xμ`). -/
noncomputable def bwdDev (Q : Measure ℝ) : ℝ≥0∞ :=
  if Integrable (fun z : ℝ => z) Q then
    ⨆ x : ℝ, ⨆ (_ : 0 < x),
      if Integrable (fun z : ℝ => Real.exp (-(x * z))) Q then
        ENNReal.ofReal (Real.sqrt (2 * (∫ z, z ∂Q) / x +
          2 / x ^ 2 * Real.log (∫ z, Real.exp (-(x * z)) ∂Q)))
      else ⊤
  else ⊤

end DDROFB


