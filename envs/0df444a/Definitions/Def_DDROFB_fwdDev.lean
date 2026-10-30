-- Prove2me | Definitions.Def_DDROFB_fwdDev
-- name    : DDROFB_fwdDev
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:03:45.499472+00:00
-- url     : https://prove2.me/theorems/5d9558dd-ce40-466d-be99-6050ea93e308
-- title:
--   Forward deviation $\sigma_f(\mathbb P_i)$ of a univariate law
-- statement:
--   Let $\mathbb Q$ be a probability measure on $\mathbb R$ with mean $\mu = \mathbb E^{\mathbb Q}[\tilde z]$. Its **forward deviation** is
--
--   $$
--   \sigma_f(\mathbb Q) \;=\; \sup_{x>0} \sqrt{-\frac{2\mu}{x} + \frac{2}{x^2}\log\mathbb E^{\mathbb Q}\bigl[e^{x\tilde z}\bigr]} \;\in [0,\infty].
--   $$
--
--   It controls the right tail of $\tilde z$: $\log\mathbb E[e^{x(\tilde z-\mu)}] \le x^2\sigma_f(\mathbb Q)^2/2$ for every $x>0$, so a finite forward deviation is a sub-Gaussian-type bound on upward deviations from the mean. It is finite, for example, whenever $\mathbb Q$ has bounded support, and equals the standard deviation for a Gaussian law.
--
--   **Formalization Note** The value is an extended nonnegative real. If the mean does not exist, the value is $+\infty$; if $\mathbb E[e^{x\tilde z}] = \infty$ for some $x>0$, the term for that $x$ is $+\infty$. This keeps Lean's default values ($\int = 0$ for a non-integrable function, $\log 0 = 0$) from giving a heavy-tailed law a small finite deviation. For a probability measure the radicand is nonnegative by Jensen's inequality, so the square root is never truncated.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (20), p. 18

import Mathlib
open MeasureTheory Classical
open scoped ENNReal

namespace DDROFB

/-- **Forward deviation** `σ_f(P_i)` of a univariate law, eq. (20).
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (20), p. 18:
"for a known (univariate) distribution `P_i` define its forward and backward deviations by
`σ_fi(P_i) = sup_{x>0} √(−2μ_i/x + (2/x²) log(E^{P_i}[e^{x ũ_i}]))`, …, where `E^{P_i}[ũ_i] = μ_i`."

`fwdDev Q` is the supremum over `x > 0` of `√(−2μ/x + (2/x²) log ∫ e^{xz} dQ(z))`, with
`μ = ∫ z dQ(z)`, as an extended nonnegative real.

**Formalization Note.** The value lies in `ℝ≥0∞`: the paper's supremum is over nonnegative reals
and is `+∞` for heavy right tails ("A sufficient, but not necessary, condition for
`σ_fi(P_i), σ_bi(P_i)` to be finite is that `P_i` has bounded support", p. 18). When the mean
`μ` does not exist (`z ↦ z` not integrable) the value is `⊤`, and for an `x > 0` at which the
moment generating function `E[e^{xz}]` is infinite (`z ↦ e^{xz}` not integrable) the term is
`⊤`; this prevents Lean's default values `∫ = 0`, `log 0 = 0` from giving a heavy-tailed law a
small finite deviation. For a probability measure the radicand is `≥ 0` by Jensen's inequality
(`log E[e^{xz}] ≥ xμ`), so `Real.sqrt` never truncates. The definition is applied only to marginals
of probability measures. -/
noncomputable def fwdDev (Q : Measure ℝ) : ℝ≥0∞ :=
  if Integrable (fun z : ℝ => z) Q then
    ⨆ x : ℝ, ⨆ (_ : 0 < x),
      if Integrable (fun z : ℝ => Real.exp (x * z)) Q then
        ENNReal.ofReal (Real.sqrt (-2 * (∫ z, z ∂Q) / x +
          2 / x ^ 2 * Real.log (∫ z, Real.exp (x * z) ∂Q)))
      else ⊤
  else ⊤

end DDROFB


