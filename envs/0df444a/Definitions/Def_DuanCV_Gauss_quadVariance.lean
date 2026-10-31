-- Prove2me | Definitions.Def_DuanCV_Gauss_quadVariance
-- name    : DuanCV_Gauss_quadVariance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:34.797719+00:00
-- url     : https://prove2.me/theorems/d33f61c8-4112-4368-8b2f-1ec3c0e2cf82
-- title:
--   The variance $\langle(\Delta(w\cdot\hat r))^2\rangle_\rho$ of a quadrature
-- statement:
--   For a two-mode state $\rho$ and $w\in\mathbb R^4$, the variance
--
--   $$\bigl\langle(\Delta(w\cdot\hat r))^2\bigr\rangle_\rho\in[0,\infty]$$
--
--   is the variance of the law of $w\cdot\hat r$ in $\rho$. It is $+\infty$ when the second moment of the law is infinite.
--
--   This is the quantity the criterion of the paper bounds. It is defined from the state itself, not from a covariance matrix: the formula $\tfrac12 w^TVw$ for Gaussian states is a theorem of this mission.
--
--   **Formalization Note** The variance is an infimum over the laws of $w\cdot\hat r$, of which there is at most one, so it is the variance of that law. It takes values in $\mathbb R_{\ge0}\cup\{\infty\}$, so an infinite variance is not replaced by a default value.
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Eq. (3), p. 2

import Mathlib
import Definitions.Def_DuanCV_Gauss_IsQuadratureLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P19 (DensityKernel)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace DuanCV.Gauss

/-- **The variance `⟨(Δ(w·r̂))²⟩_ρ` of a quadrature observable.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Eq. (3), p. 2.

The variance, in `ℝ≥0∞`, of the law of `w·r̂` in `ρ`; it is `⊤` when the second moment is infinite.

**Formalization Note.** The law is unique (`IsQuadratureLaw`), so the infimum is the variance of
that one law. The value would be `⊤` if no law existed, which does not happen for a density
operator. `evariance` centres at the Bochner mean, which is `0` for a non-integrable law, but such
a law has infinite second moment, so the value is `⊤` there as it should be. The variance is not
defined through a covariance matrix: for Gaussian states `½ wᵀVw` is a theorem
(`gaussian_quadrature_variance`). -/
noncomputable def quadVariance (ρ : DensityKernel 2) (w : QuadratureIndex 2 → ℝ) : ℝ≥0∞ :=
  ⨅ (μ : Measure ℝ) (_ : IsQuadratureLaw ρ w μ), evariance id μ

end DuanCV.Gauss


