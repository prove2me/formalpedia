-- Prove2me | Definitions.Def_ImpliedAmbiguity_thetaBar
-- name    : ImpliedAmbiguity_thetaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:05.396108+00:00
-- url     : https://prove2.me/theorems/b627e379-3a7d-4a19-8c6e-c48d07b39bca
-- title:
--   The bound $\bar\theta = (\mu-R_f\mathbf 1)^\top x / x^\top\Sigma_R x$ on risk aversion
-- statement:
--   Let $\Sigma_R$ be the $N\times N$ covariance matrix of asset returns, $c = \mu - R_f\mathbf 1$ the expected excess return vector and $x \in \mathbb R^N$ a portfolio of risky assets. Define
--
--   $$
--   \bar\theta = \frac{c^\top x}{x^\top \Sigma_R x}. \tag{15}
--   $$
--
--   When $c^\top x > 0$, $\bar\theta$ is an upper bound on the coefficient of absolute risk aversion $\theta$ of any ambiguity-averse investor for whom $x$ is optimal (Theorem 2). In Lemma 4 the same number is written $\bar\theta = (x^\top\Sigma x)^{-1}(x\cdot c)$.
--
--   **Formalization Note** The excess return vector is an argument `c` (the theorems pass `excessReturn μ Rf`). The division is Lean's total division; all theorems assume $\Sigma_R$ positive definite and $c^\top x > 0$, so the denominator is positive.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), eq. (15), p.18; Appendix C, Lemma 4, p.41

import Mathlib

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
eq. (15), p.18: `θ̄ = (µ − R_f 1)ᵀx / xᵀΣ_R x`, the upper bound on the coefficient of absolute
risk aversion of an investor for whom the portfolio `x` is optimal. Appendix C, Lemma 4, p.41
writes the same number as `θ̄ = (xᵀΣx)⁻¹(x · c)`.

**Formalization Note.** The excess return vector `µ − R_f 1` is passed as `c` (instantiated with
`excessReturn μ Rf` in the theorems, and with Lemma 4's `c` there); `(µ − R_f1)ᵀx` is
`c ⬝ᵥ x` and `xᵀΣ_R x` is `x ⬝ᵥ (SigmaR *ᵥ x)`. The division is Lean's total division; every
theorem assumes `Σ_R` positive definite and `c ⬝ᵥ x > 0` (so `x ≠ 0` and the denominator is
positive). -/
noncomputable def thetaBar {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (c x : Fin N → ℝ) : ℝ :=
  (c ⬝ᵥ x) / (x ⬝ᵥ (SigmaR *ᵥ x))

end ImpliedAmbiguity


