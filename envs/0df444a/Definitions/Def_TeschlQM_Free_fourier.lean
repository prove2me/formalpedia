-- Prove2me | Definitions.Def_TeschlQM_Free_fourier
-- name    : TeschlQM_Free_fourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T23:56:34.227526+00:00
-- url     : https://prove2.me/theorems/45d0938a-a93b-480a-b377-9a0886fa3205
-- title:
--   Fourier transform in Teschl's normalization (7.3), its inverse (7.8), and ψ̂ for ψ ∈ L²
-- statement:
--   Write $\mathbb R^n$ for $n$-dimensional Euclidean space, with inner product $px = \sum_j p_j x_j$ and $x^2 = |x|^2$. For a function $f : \mathbb R^n \to \mathbb C$ the **Fourier transform** is
--   $$\mathcal F(f)(p) = \hat f(p) = \frac{1}{(2\pi)^{n/2}} \int_{\mathbb R^n} e^{-ipx} f(x)\, d^n x,$$
--   and the **inverse Fourier transform** is
--   $$\mathcal F^{-1}(g)(x) = \check g(x) = \frac{1}{(2\pi)^{n/2}} \int_{\mathbb R^n} e^{ipx} g(p)\, d^n p .$$
--   For $\psi \in L^2(\mathbb R^n)$, $\hat\psi$ denotes the $L^2$ Fourier transform in the same normalization, the unitary extension of $\mathcal F$ from $L^1 \cap L^2$ to $L^2$.
--
--   These are the transforms in terms of which the free Schrödinger operator, its time evolution and all Fourier identities of the chapter are stated.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so $px$ and $x^2$ are Euclidean. `fourier n f` and `fourierInv n g` are the integrals above with the prefactor $(2\pi)^{-n/2}$; they are not Mathlib's `𝓕`, which uses $e^{-2\pi i\langle x,\xi\rangle}$ and no prefactor. The Bochner integral is $0$ for non-integrable integrands, so every statement about `fourier` carries an integrability or Schwartz hypothesis. `fourierL2 n ψ` is Teschl's $\hat\psi$ for $\psi \in L^2$, built from Mathlib's unitary $L^2$ transform `𝓕` by the rescaling identity $\hat\psi(p) = (2\pi)^{-n/2} (\mathcal F_{\mathrm{Mathlib}}\psi)(p/(2\pi))$; it is a function determined up to a null set. That it is the unitary extension of $\mathcal F$ is Theorem 7.5 of this mission.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 161, Section 7.1, Eq. (7.3); p. 163, Eq. (7.8); p. 164, Eq. (7.10)

import Mathlib

namespace TeschlQM.Free

open MeasureTheory FourierTransform
open scoped InnerProductSpace

/-- Teschl (7.3), p. 161: the Fourier transform in Teschl's normalization,
`F(f)(p) = f̂(p) = (2π)^{-n/2} ∫_{ℝⁿ} e^{-ipx} f(x) dⁿx`, on `ℝⁿ = EuclideanSpace ℝ (Fin n)`
(so `px = ⟪p, x⟫` and `x² = ‖x‖²` are Euclidean). This is **not** Mathlib's `𝓕`, which uses
`e^{-2πi⟪x, ξ⟫}` and no prefactor. For `f` not integrable the Bochner integral is `0`. -/
noncomputable def fourier (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (p : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
    ∫ x : EuclideanSpace ℝ (Fin n), Complex.exp (-(⟪p, x⟫_ℝ : ℂ) * Complex.I) * f x

/-- Teschl (7.8), p. 163: the inverse Fourier transform in Teschl's normalization,
`F⁻¹(g)(x) = ǧ(x) = (2π)^{-n/2} ∫_{ℝⁿ} e^{ipx} g(p) dⁿp`. -/
noncomputable def fourierInv (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
    ∫ p : EuclideanSpace ℝ (Fin n), Complex.exp ((⟪p, x⟫_ℝ : ℂ) * Complex.I) * g p

/-- Teschl, p. 164 (Theorem 7.5, (7.10)): the Fourier transform `ψ̂` of `ψ ∈ L²(ℝⁿ)` in Teschl's
normalization, obtained from Mathlib's unitary `L²` Fourier transform `𝓕` (normalization
`e^{-2πi⟪x, ξ⟫}`) through the rescaling identity `ψ̂(p) = (2π)^{-n/2} (𝓕ψ)(p / (2π))`.
The value is a function `ℝⁿ → ℂ`, determined up to a null set (it is built from an almost
everywhere defined representative of `𝓕ψ`). -/
noncomputable def fourierL2 (n : ℕ)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (p : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
    (𝓕 ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ((2 * Real.pi)⁻¹ • p)

end TeschlQM.Free


