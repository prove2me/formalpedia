-- Prove2me | Definitions.Def_GrothendieckLB_gaussExp
-- name    : GrothendieckLB_gaussExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:25.155202+00:00
-- url     : https://prove2.me/theorems/844ddc69-7adf-4f3e-b838-efba9cb47945
-- title:
--   Gaussian expectation $\mathbb E[F(X)]$, $X\sim N(0,I_d)$
-- statement:
--   For $F:\mathbb R^d\to\mathbb R$, this is the expectation $\mathbb E[F(X)]$ of $F$ under a standard Gaussian vector $X\sim N(0,I_d)$,
--   $$
--   \mathbb E[F(X)]=\int_{\mathbb R^d}F(x)\prod_{m=1}^d\varphi(x_m)\,dx,\qquad \varphi(s)=\frac{e^{-s^2/2}}{\sqrt{2\pi}} .
--   $$
--   It is the Gaussian inner product $\langle F,G\rangle=\mathbb E[F(X)G(X)]$ of Section 7 applied to one function, and every Hermite coefficient of the mission is such an expectation.
--
--   **Formalization Note** The product-density form matches the published `GrothendieckConstant.coeff_hermite_moments`. Every use takes $F$ measurable with polynomial growth, so the integrand is integrable and the Bochner integral is the true expectation.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.30

import Mathlib
open MeasureTheory ProbabilityTheory

namespace GrothendieckLB

/-- Gaussian expectation `E[F(X)]` for `X ∼ N(0, I_d)` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.30).

**Formalization Note** The expectation is the integral against the product density
`∏ m, gaussianPDFReal 0 1 (x m)`, the form used by the published
`GrothendieckConstant.coeff_hermite_moments`. Every use takes `F` measurable and of polynomial
growth, so the integrand is integrable and the Bochner integral is the true expectation. -/
noncomputable def gaussExp {d : ℕ} (F : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x, F x * ∏ m, gaussianPDFReal 0 1 (x m)

end GrothendieckLB


