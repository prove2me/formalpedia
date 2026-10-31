-- Prove2me | Definitions.Def_ForkJoinDelay_boundaryLST
-- name    : ForkJoinDelay_boundaryLST
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:42.602986+00:00
-- url     : https://prove2.me/theorems/19c6250a-5195-4502-9df0-1b7e877c115c
-- title:
--   The boundary transform $Z_{x,y}(w_{FJ})$
-- statement:
--   For rates $\mu_1,\mu_2$, integers $x,y$ and a transform argument $w_{FJ}$,
--
--   $$Z_{x,y}(w_{FJ})=\int e^{-w_{FJ}\max(s,t)}\,d\bigl(\Gamma(x,\mu_1)\otimes\Gamma(y,\mu_2)\bigr)(s,t),$$
--
--   the Laplace–Stieltjes transform of the maximum of independent random variables with laws $\Gamma(x,\mu_1)$ and $\Gamma(y,\mu_2)$ (shape, rate). It is the transform of the fork-join sojourn time of a tagged customer who finds $x-1$ customers at UFJ and $y-1$ at LFJ, so that $x$ and $y$ count the tagged customer; its sojourn times there are sums of $x$ and $y$ exponential services.
--
--   **Formalization Note** Mathlib's gamma measure takes shape and rate. Only $x,y\ge1$ are used; for shape $0$ Mathlib's gamma measure is the zero measure.
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §3.1, Eq. (5), p.12, and the paragraph after it ((S1|h1 = x) ∼ Gamma(x,µ1), (S2|h2 = y) ∼ Gamma(y,µ2))

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ForkJoinDelay

/-- **The boundary transform `Z_{x,y}(w_FJ)`.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §3.1, Eq. (5), p.12: "We define Zx,y(wFJ) as the LST of the total
sojourn time of the tagged customer in the FJ part, given that there are x customers at the UFJ
station and y customers at the LFJ station (including the tagged customer)",
`Z_{x,y}(w_FJ) := E[e^{−w_FJ S_FJ} | h₁ = x, h₂ = y] = ∫₀^∞ e^{−w_FJ t} dF_{S_FJ|x,y}(t)`;
and p.12: "(S1|h1 = x) ∼ Gamma(x,µ1), (S2|h2 = y) ∼ Gamma(y,µ2)", independent.

`boundaryLST μ₁ μ₂ x y wFJ = ∫ exp (-w_FJ · max s t) d(Gamma(x, µ₁) ⊗ Gamma(y, µ₂))(s, t)`.

**Formalization Note.** Mathlib's `gammaMeasure a r` has shape `a` and **rate** `r` (mean
`a / r`), matching the sum of `x` exponential services of rate `µ₁`; the shape is the cast
`(x : ℝ)`. Only `x, y ≥ 1` occur (the tagged customer is counted); for `x = 0` Mathlib's
`gammaMeasure 0 r` is the zero measure. The milestone `sec_3_1_fj_cdf` connects this product
law to sums of exponential services and to the CDF display of p.12. -/
noncomputable def boundaryLST (μ₁ μ₂ : ℝ) (x y : ℕ) (wFJ : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ, Complex.exp (-(wFJ * ((max p.1 p.2 : ℝ) : ℂ)))
    ∂((gammaMeasure (x : ℝ) μ₁).prod (gammaMeasure (y : ℝ) μ₂))

end ForkJoinDelay


