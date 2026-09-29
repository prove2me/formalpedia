-- Prove2me | Definitions.Def_FastFourierTransform_dft
-- name    : FastFourierTransform_dft
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T18:03:19.60431+00:00
-- url     : https://prove2.me/theorems/462bd31d-c561-4449-9102-a20c09b1cced
-- title:
--   Discrete Fourier transform $X_k=\sum_m x_m e^{-2\pi i mk/n}$
-- statement:
--   The **discrete Fourier transform** (DFT) of length $n$. A signal is a function $x:\mathbb{N}\to\mathbb{C}$, and its transform of length $n$ at frequency index $k$ is
--
--   $$\mathrm{dft}(n,x)(k)=\sum_{m=0}^{n-1} x_m\, e^{-2\pi i\,mk/n}.$$
--
--   Only the samples $x_0,\dots,x_{n-1}$ enter the sum, and the frequency index $k$ ranges over all natural numbers (the transform is $n$-periodic in $k$). For $n=0$ the sum is empty, so the value is $0$. This is the unnormalized convention with the minus sign in the exponent; the $1/n$ factor is carried by the inverse transform.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, section 'Definition'

import Mathlib

namespace FastFourierTransform

/-- The discrete Fourier transform (DFT) of length `n`:
`dft n x k = ∑_{m < n} x m * exp (-2 π i m k / n)`. -/
noncomputable def dft (n : ℕ) (x : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ m ∈ Finset.range n,
    x m * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k : ℂ) / (n : ℂ)))

end FastFourierTransform


