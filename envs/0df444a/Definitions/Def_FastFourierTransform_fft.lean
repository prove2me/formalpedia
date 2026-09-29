-- Prove2me | Definitions.Def_FastFourierTransform_fft
-- name    : FastFourierTransform_fft
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T18:08:19.734995+00:00
-- url     : https://prove2.me/theorems/4815be50-2f71-4782-a91a-c2e18b8ee715
-- title:
--   Radix-2 Cooley–Tukey FFT recursion
-- statement:
--   The **radix-2 Cooley–Tukey fast Fourier transform** on $n=2^p$ sample points, as a recursion on the exponent $p$:
--
--   $$\mathrm{fft}(0,x)(k)=x_0,$$
--
--   $$\mathrm{fft}(p+1,x)(k)=E\big(k \bmod 2^p\big)+e^{-2\pi i k/2^{p+1}}\cdot O\big(k \bmod 2^p\big),$$
--
--   where $E=\mathrm{fft}(p,\;m\mapsto x_{2m})$ transforms the even-indexed subsequence and $O=\mathrm{fft}(p,\;m\mapsto x_{2m+1})$ the odd-indexed one, and $e^{-2\pi i k/2^{p+1}}$ is the **twiddle factor** of the merge stage. The definition is purely algorithmic: it never mentions the DFT. The index $k$ is an arbitrary natural number and the sub-transforms are evaluated at the reduced index $k \bmod 2^p$.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, section 'Algorithms — Cooley–Tukey algorithm' (radix-2, decimation in time)

import Mathlib

namespace FastFourierTransform

/-- The radix-2 Cooley–Tukey fast Fourier transform on `2 ^ p` sample points.
`fft 0 x` is the constant map `x 0`; `fft (p + 1) x k` combines the transforms of the
even-indexed and odd-indexed subsequences with the twiddle factor
`exp (-2 π i k / 2 ^ (p + 1))`. -/
noncomputable def fft : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, x, _ => x 0
  | (p + 1), x, k =>
      fft p (fun m => x (2 * m)) (k % 2 ^ p)
        + Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / ((2 : ℂ) ^ (p + 1))))
            * fft p (fun m => x (2 * m + 1)) (k % 2 ^ p)

end FastFourierTransform


