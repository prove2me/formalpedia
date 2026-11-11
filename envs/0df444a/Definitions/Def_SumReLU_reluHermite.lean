-- Prove2me | Definitions.Def_SumReLU_reluHermite
-- name    : SumReLU_reluHermite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:38.932054+00:00
-- url     : https://prove2.me/theorems/a49cde5d-17fa-47fd-8850-d3a499452c81
-- title:
--   Hermite coefficients $\hat\sigma_p$ of the ReLU
-- statement:
--   Let $\mathrm{he}_p=\mathrm{He}_p/\sqrt{p!}$ be the normalized probabilists' Hermite polynomials, an orthonormal basis of $L^2(N(0,1))$. The $p$-th Hermite coefficient of the ReLU is
--   $$
--   \hat\sigma_p=\mathbb E_{z\sim N(0,1)}\big[\sigma(z)\,\mathrm{he}_p(z)\big].
--   $$
--   It is the normalizing constant in the moment identity (4), in the filtered matrix (M) and in the STC tensor (20); it is nonzero for $p=0$ and every even $p$.
--
--   **Formalization Note** Defined as the integral, not through the closed form of Fact 2.4 (a cited fact). $\mathrm{he}_p$ is the published `GaussPart.hermiteOne`, built on Mathlib's `Polynomial.hermite`.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), §2, (5), p.10 (PDF p.12) and p.11 (PDF p.13)

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SumReLU_reluSum

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- The `p`-th Hermite coefficient of the ReLU, `σ̂_p = E_{z∼N(0,1)}[σ(z) he_p(z)]`, with
`he_p = He_p/√(p!)` the normalized probabilists' Hermite polynomial (published
`GaussPart.hermiteOne`, Mathlib's `Polynomial.hermite`).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), §2, p.10 (PDF p.12), (5): "f̂_p := E_{z∼N(0,1)}[f(z)he_p(z)]"; p.11 (PDF p.13): "we denote by
σ̂_i the ith Hermite coefficient of the ReLU function σ".

**Formalization Note.** Defined as the integral, not by the closed form of Fact 2.4 (a cited fact).
`σ(z) he_p(z)` has polynomial growth, so the integral is a genuine Gaussian integral. -/
noncomputable def reluHermite (p : ℕ) : ℝ :=
  ∫ z, relu z * GaussPart.hermiteOne p z ∂(gaussianReal 0 1)

end SumReLU


