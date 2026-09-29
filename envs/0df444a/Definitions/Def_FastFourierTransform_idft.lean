-- Prove2me | Definitions.Def_FastFourierTransform_idft
-- name    : FastFourierTransform_idft
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T18:04:00.839575+00:00
-- url     : https://prove2.me/theorems/a17945fd-35f6-4833-a03a-531a64f6a037
-- title:
--   Inverse discrete Fourier transform $x_m=\frac1n\sum_k X_k e^{2\pi i mk/n}$
-- statement:
--   The **inverse discrete Fourier transform** (IDFT) of length $n$: for a spectrum $X:\mathbb{N}\to\mathbb{C}$,
--
--   $$\mathrm{idft}(n,X)(m)=\frac1n\sum_{k=0}^{n-1} X_k\, e^{+2\pi i\,mk/n}.$$
--
--   It is the transform with the opposite sign in the exponent together with the normalizing factor $1/n$. For $n=0$ the sum is empty and the factor $1/n$ is $0$ by the usual convention, so the value is $0$.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, section 'Definition' ('the inverse DFT is the same as the DFT, but with the opposite sign in the exponent and a 1/n factor')

import Mathlib

namespace FastFourierTransform

/-- The inverse discrete Fourier transform (IDFT) of length `n`:
`idft n X m = (1 / n) * ∑_{k < n} X k * exp (2 π i m k / n)`. -/
noncomputable def idft (n : ℕ) (X : ℕ → ℂ) (m : ℕ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k ∈ Finset.range n,
    X k * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k : ℂ) / (n : ℂ))

end FastFourierTransform


