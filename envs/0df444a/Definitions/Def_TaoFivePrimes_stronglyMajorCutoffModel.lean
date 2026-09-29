-- Prove2me | Definitions.Def_TaoFivePrimes_stronglyMajorCutoffModel
-- name    : TaoFivePrimes_stronglyMajorCutoffModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-09T13:10:10.698248+00:00
-- url     : https://prove2.me/theorems/1e9a2d48-7c78-4af8-8ff3-8adf4b2b247e
-- title:
--   Centered Fourier cutoff model on the unit circle
-- statement:
--   For a real cutoff $\eta$, a real scale $y$, and a point $\alpha\in\mathbb R/\mathbb Z$, let $\widetilde\alpha\in[-1/2,1/2)$ be the centered representative of $\alpha$. Define
--   $$E_{\eta,y}(\alpha)=\int_{\mathbb R}\eta(t)\exp\!\left(2\pi i\,y\widetilde\alpha t\right)\,dt.$$
--   This is the ordinary Fourier transform model, with Tao's positive-phase convention $e(u)=e^{2\pi i u}$, used to approximate the two sifted prime sums on the strongly major arc in Section 8.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 8, especially the Fourier models in eqs. 8.13–8.16, https://arxiv.org/html/1201.6656v4

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace TaoFivePrimes

/-- The ordinary real Fourier transform of a cutoff, evaluated at the centered
representative of `alpha : ℝ / ℤ` and a real scale.  This uses Tao's convention
`e(u) = exp(2 * pi * i * u)`. -/
noncomputable def stronglyMajorCutoffModel (eta : ℝ → ℝ) (scale : ℝ)
    (alpha : AddCircle (1 : ℝ)) : ℂ :=
  ∫ t : ℝ, (eta t : ℂ) *
    Complex.exp
      (2 * Real.pi * Complex.I *
        ((scale * AddCircle.liftIoc (1 : ℝ) (-(1 / 2 : ℝ)) id alpha) * t))

end TaoFivePrimes


