-- Prove2me | Definitions.Def_HunterPDE_Semilinear_SobolevHs
-- name    : HunterPDE_Semilinear_SobolevHs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:11:33.253267+00:00
-- url     : https://prove2.me/theorems/3df096a0-cc7a-47ef-b447-349ecb32f350
-- title:
--   The book's Fourier transform on L²(ℝⁿ) and the fractional Sobolev norm ‖·‖_{Hˢ} (Definitions 5.64, 5.74)
-- statement:
--   Write $\mathbb{R}^n$ for Euclidean space with Lebesgue measure. For $f \in L^2(\mathbb{R}^n)$ (complex-valued) the **Fourier transform** in the normalization of the notes is
--   $$\hat f(k) = \frac{1}{(2\pi)^n} \int_{\mathbb{R}^n} f(x)\, e^{-ik\cdot x}\, dx,$$
--   defined by this integral for Schwartz functions and extended to $L^2$ by Plancherel's theorem. With $\langle k\rangle = (1+|k|^2)^{1/2}$, the **Sobolev norm** of order $s \ge 0$ is
--   $$\|f\|_{H^s} = \Big( (2\pi)^n \int_{\mathbb{R}^n} \langle k\rangle^{2s}\, |\hat f(k)|^2\, dk \Big)^{1/2},$$
--   and $H^s(\mathbb{R}^n)$ consists of the $f \in L^2$ for which it is finite. With this normalization $\|f\|_{H^0} = \|f\|_{L^2}$.
--
--   These are the fractional $L^2$-Sobolev spaces in which the semilinear heat equation of §5.5 is solved: the solution is a continuous curve in $H^{2\alpha}(\mathbb{R}^n)$.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. The $L^2$ Fourier transform is Mathlib's `Lp.fourierTransformₗᵢ` (the $L^2$ extension of $\int f(x)e^{-2\pi i\langle x,\xi\rangle}dx$), converted to the book's normalization by $\hat f(k) = (2\pi)^{-n}\,\mathcal F f(k/2\pi)$. The norm `hsNorm n s f` is valued in $[0,\infty]$ and equals $\infty$ when $f \notin L^2$ or the weighted integral diverges, so $f \in H^s$ is `hsNorm n s f < ⊤`. The factor $(2\pi)^n$ is placed inside the square root, as in the book's inner product $(f,g)_{H^s}$ and in the computation on p. 154; Definition 5.74 prints it outside the root, which contradicts both. `hsNormReal` is the same norm for a real-valued function.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 168, Definition 5.64; p. 172, Definition 5.74

import Mathlib

open MeasureTheory
open scoped ENNReal FourierTransform

namespace HunterPDE.Semilinear

/-- The Fourier transform of an `L²(ℝⁿ)` function in the normalization of Hunter, *Notes on PDEs*,
Definition 5.64, (5.73) (p. 168):
`f̂(k) = 1/(2π)ⁿ ∫_{ℝⁿ} f(x) e^{−i k·x} dx`,
extended from Schwartz functions to `L²` by Plancherel's theorem (p. 172: "a function belongs to
`L²` if and only if its Fourier transform belongs to `L²`").

Here `ℝⁿ = EuclideanSpace ℝ (Fin n)`. Mathlib's `L²` Fourier transform
`MeasureTheory.Lp.fourierTransformₗᵢ` is the `L²` extension of
`𝓕 f(ξ) = ∫ f(x) e^{−2πi⟨x,ξ⟩} dx`, so on Schwartz functions the book's transform is
`f̂(k) = (2π)^{−n} · 𝓕 f(k / (2π))`, and this is the formula used here. `f̂` is an element of
`L²`; the function below is one representative of it (every quantity built from it in this
mission is an integral, which does not depend on the representative). -/
noncomputable def fourierL2 (n : ℕ) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (k : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ((((2 * Real.pi) ^ n)⁻¹ : ℝ) : ℂ) *
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ f) ((2 * Real.pi)⁻¹ • k)

open scoped Classical in
/-- The `Hˢ(ℝⁿ)` norm of Hunter, *Notes on PDEs*, Definition 5.74 (p. 172), for `s ≥ 0` and a
complex-valued function `f` on `ℝⁿ`, with `⟨k⟩ = (1 + |k|²)^{1/2}`:
`‖f‖_{Hˢ} = ( (2π)ⁿ ∫_{ℝⁿ} ⟨k⟩^{2s} |f̂(k)|² dk )^{1/2}`,
where `f̂` is the book's Fourier transform (`fourierL2`). `⟨k⟩^{2s}` is written `(1 + |k|²)^s`.

The factor `(2π)ⁿ` sits inside the square root, as in the book's inner product
`(f, g)_{Hˢ} = (2π)ⁿ ∫ ⟨k⟩^{2s} f̂ ḡ̂ dk` (same Definition) and in the computation of
`‖e^{−tA}h‖²_{H^{2α}}` on p. 154; with it `‖f‖_{H⁰} = ‖f‖_{L²}` (Parseval).

The value is in `[0, ∞]`: it is `∞` when `f ∉ L²(ℝⁿ)` and when the weighted integral diverges.
So, for `s ≥ 0`, `f ∈ Hˢ(ℝⁿ)` exactly when `hsNorm n s f < ∞` (for `s ≥ 0` every element of
`Hˢ` is an `L²` function). -/
noncomputable def hsNorm (n : ℕ) (s : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : ℝ≥0∞ :=
  if hf : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) then
    (ENNReal.ofReal ((2 * Real.pi) ^ n) *
        ∫⁻ k, ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ s) * ‖fourierL2 n (hf.toLp f) k‖ₑ ^ 2) ^ (1 / 2 : ℝ)
  else ⊤

/-- The `Hˢ(ℝⁿ)` norm (`hsNorm`) of a real-valued function, viewed as complex-valued. -/
noncomputable def hsNormReal (n : ℕ) (s : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  hsNorm n s (fun x => (f x : ℂ))

end HunterPDE.Semilinear


