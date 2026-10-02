-- Prove2me | Definitions.Def_HunterPDE_HeatFourier_FourierTransform
-- name    : HunterPDE_HeatFourier_FourierTransform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:56:45.415699+00:00
-- url     : https://prove2.me/theorems/adf2a4cb-1edf-4bda-bbe9-c0d0a40c223d
-- title:
--   Definition 5.64 and Definition 5.74 — the Fourier transform with the (2π)^{−n} normalization, and the Hˢ(ℝⁿ) norm
-- statement:
--   The **Fourier transform** of $f : \mathbb{R}^n \to \mathbb{C}$ (for $f$ in the Schwartz space) is
--   $$\hat f(k) = \frac{1}{(2\pi)^n} \int_{\mathbb{R}^n} f(x)\, e^{-ik\cdot x}\, dx .$$
--   With $\langle k\rangle = (1+|k|^2)^{1/2}$, the **Sobolev norm** of order $s \in \mathbb{R}$ is
--   $$\|f\|_{H^s} = \Big( (2\pi)^n \int_{\mathbb{R}^n} \langle k\rangle^{2s}\, |\hat f(k)|^2\, dk \Big)^{1/2}.$$
--   With this normalization Parseval's identity reads $\int |f|^2\,dx = (2\pi)^n \int |\hat f|^2\,dk$, so $\|f\|_{H^0} = \|f\|_{L^2}$.
--
--   **Formalization Note.** This is the book's normalization, not Mathlib's `𝓕` (which uses $e^{-2\pi i\langle x,\xi\rangle}$ and no prefactor). $k\cdot x$ is the Euclidean inner product. The $H^s$ norm is valued in $[0,\infty]$ (a lower Lebesgue integral), and $\langle k\rangle^{2s}$ is written $(1+|k|^2)^s$. Both are applied only to Schwartz functions, where the Fourier integral converges absolutely and the norm is finite; the space $H^s$ itself (tempered distributions) is not needed by this mission's statements.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 168, Definition 5.64, Eq. (5.73); p. 172, Definition 5.74

import Mathlib

namespace HunterPDE.HeatFourier

open MeasureTheory
open scoped ENNReal

/-- The Fourier transform in the normalization of Hunter, *Notes on PDEs*, Definition 5.64,
(5.73) (p. 168):
`f̂(k) = 1/(2π)ⁿ ∫_{ℝⁿ} f(x) e^{−i k·x} dx`,
for `f : ℝⁿ → ℂ`, `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `k·x` the Euclidean inner product. This is
*not* Mathlib's `𝓕` (which uses `e^{−2πi⟨x,ξ⟩}` and no prefactor). It is applied only to
Schwartz functions, for which the integral converges absolutely. -/
noncomputable def fourierTransform (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (k : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ((1 / (2 * Real.pi) ^ n : ℝ) : ℂ) *
    ∫ x, f x * Complex.exp (-(Complex.I * ((inner ℝ k x : ℝ) : ℂ)))

/-- The `Hˢ(ℝⁿ)` norm of Hunter, *Notes on PDEs*, Definition 5.74 (p. 172), with
`⟨k⟩ = (1 + |k|²)^{1/2}`:
`‖f‖_{Hˢ} = ( (2π)ⁿ ∫ ⟨k⟩^{2s} |f̂(k)|² dk )^{1/2}`,
where `f̂` is the book's Fourier transform `fourierTransform` (5.73). This is the norm of the
book's `Hˢ` inner product `(f, g)_{Hˢ} = (2π)ⁿ ∫ ⟨k⟩^{2s} f̂ ḡ̂ dk`; the norm formula printed on
p. 172 puts `(2π)ⁿ` outside the square root, which is inconsistent with that inner product and
with `‖f‖_{H⁰} = ‖f‖_{L²}`. The two differ by the constant factor `(2π)^{n/2}`. `⟨k⟩^{2s}` is written
`(1 + |k|²)^s`. The integral is a lower Lebesgue integral in `[0, ∞]`, so the norm is
`ℝ≥0∞`-valued and is `∞` exactly when the weighted integral diverges. It is applied only to
Schwartz functions (for which it is finite). -/
noncomputable def hsNorm (n : ℕ) (s : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal ((2 * Real.pi) ^ n) *
      ∫⁻ k, ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ s) * ‖fourierTransform n f k‖ₑ ^ 2) ^ (1 / 2 : ℝ)

end HunterPDE.HeatFourier


