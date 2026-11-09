-- Prove2me | Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
-- name    : BLTCounting_AccuracySpace_FourierKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:30.602097+00:00
-- url     : https://prove2.me/theorems/ac8f00f8-182d-4513-a59a-6b3fca828cc1
-- title:
--   The kernel $c_0$, its Fourier transform, Toeplitz symbols, the rescaled Toeplitz matrix and the band matrix
-- statement:
--   This module fixes the Fourier objects of the paper, with the transform convention $\widehat g(\omega)=\int_{\mathbb R}g(x)e^{-i\omega x}\,dx$ of equation (10).
--
--   1. The **kernel** is $c_0(t)=(2\pi)^{-1/2}\,\mathrm{sech}^{1/2}(t/2)$, and $\widehat c_0(\omega)=\int_{\mathbb R}c_0(x)e^{-i\omega x}\,dx$.
--   2. For a bilateral sequence $(a[t])_{t\in\mathbb Z}$, the **symbol** is $a(\theta)=\sum_{t\in\mathbb Z}a[t]e^{it\theta}$ and the finite **Toeplitz matrix** is $T[i,j]=a[i-j]$ for $0\le i,j<K$. For $u\in\mathbb C^K$, the **trigonometric polynomial** is $\widehat u(\theta)=\sum_{j=0}^{K-1}u[j]e^{ij\theta}$.
--   3. The **sampled-kernel symbol** is the actual series $\widehat a_h(\theta)=\sum_{t\in\mathbb Z}c_0(ht)e^{-it\theta}$.
--   4. The **rescaled Toeplitz matrix** is $V_h[i,j]=h\,c_0((i-j)h)$ for $0\le i,j<K$.
--   5. The **band matrix** is $B[i,j]=\frac1{2\pi}\int_{-\theta}^{\theta}e^{i(i-j)x}\,dx$ for $0\le i,j<K$, with coefficients $b_0=\theta/\pi$ and $b_p=\sin(p\theta)/(\pi p)$ for $p\neq0$.
--
--   These objects carry the spectral count at the heart of the lower bound. None of them is defined through the identities the mission asks to prove.
--
--   **Formalization Note.** $\widehat c_0$ is a complex Bochner integral. The verification file proves sorry-free that its integrand is integrable. The series are written with `tsum`; the statements that use them assert summability where it is not a hypothesis.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, equation (5), printed p. 6 (PDF p. 7); equations (10)-(11), printed p. 11 (PDF p. 12); Lemma 2.7, printed p. 11 (PDF p. 12); equation (18), printed p. 17 (PDF p. 18); equation (21), printed p. 18 (PDF p. 19); band matrix, printed p. 20 (PDF p. 21) and printed p. 29 (PDF p. 30); $V_h$, printed p. 27 (PDF p. 28)

import Mathlib

open Matrix Complex

namespace BLTCounting.AccuracySpace

/-- The kernel of equation (5), PDF p. 7: `c₀(t) = (2π)^{-1/2} sech^{1/2}(t/2)`. -/
noncomputable def c0 (t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (1 / Real.cosh (t / 2))

/-- The Fourier transform of `c₀`, equation (18), PDF p. 18, in the convention of equation (10):
`ĉ₀(ω) = ∫_ℝ c₀(x) e^{-iωx} dx`. It is an honest complex Bochner integral; `c₀` is integrable, as
proved in the mission's verification file. -/
noncomputable def c0Hat (ω : ℝ) : ℂ :=
  ∫ x : ℝ, (c0 x : ℂ) * cexp (-(I * ω * x))

/-- The `2π`-periodic symbol `a(θ) = ∑_{t ∈ ℤ} a[t] e^{itθ}` of a bilateral sequence (Lemma 2.7,
PDF p. 12). -/
noncomputable def bilateralSymbol (a : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑' t : ℤ, a t * cexp (I * t * θ)

/-- The trigonometric polynomial `û(θ) = ∑_{j=0}^{K-1} u[j] e^{ijθ}`, equation (11), PDF p. 12. -/
noncomputable def trigPoly {K : ℕ} (u : Fin K → ℂ) (θ : ℝ) : ℂ :=
  ∑ j : Fin K, u j * cexp (I * ((j : ℕ) : ℂ) * θ)

/-- The finite Toeplitz matrix `T[i, j] = a[i - j]`, `0 ≤ i, j < K` (Lemma 2.7, PDF p. 12). -/
def toeplitz (K : ℕ) (a : ℤ → ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  Matrix.of fun i j => a (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))

/-- The sampled-kernel Toeplitz symbol `â_h(θ) = ∑_{t ∈ ℤ} c₀(ht) e^{-itθ}`, equation (21), PDF p. 19.
It is the actual series, not a function defined by the Poisson identity. -/
noncomputable def sampledSymbol (h θ : ℝ) : ℂ :=
  ∑' t : ℤ, ((c0 (h * t) : ℝ) : ℂ) * cexp (-(I * t * θ))

/-- The rescaled Toeplitz matrix `V_h[i, j] = h c₀((i - j)h)`, `0 ≤ i, j < K` (PDF p. 28). -/
noncomputable def rescaledToeplitz (K : ℕ) (h : ℝ) : Matrix (Fin K) (Fin K) ℂ :=
  Matrix.of fun i j => ((h * c0 ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * h) : ℝ) : ℂ)

/-- The band matrix `B[i, j] = (1/2π) ∫_{-θ}^{θ} e^{i(i-j)x} dx`, `0 ≤ i, j < K` (PDF pp. 21, 30). -/
noncomputable def bandMatrix (K : ℕ) (θ : ℝ) : Matrix (Fin K) (Fin K) ℂ :=
  Matrix.of fun i j =>
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ x in (-θ)..θ, cexp (I * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) * x)

/-- The coefficients of the band matrix (PDF p. 21): `b₀ = θ/π`, and `b_p = sin(pθ)/(πp)` for
integers `p ≠ 0`. -/
noncomputable def bandCoeff (θ : ℝ) (p : ℤ) : ℝ :=
  if p = 0 then θ / Real.pi else Real.sin (p * θ) / (Real.pi * p)

end BLTCounting.AccuracySpace


