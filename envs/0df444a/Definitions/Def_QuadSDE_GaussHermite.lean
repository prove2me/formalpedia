-- Prove2me | Definitions.Def_QuadSDE_GaussHermite
-- name    : QuadSDE_GaussHermite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:19.217696+00:00
-- url     : https://prove2.me/theorems/92ad722f-28f4-4ecb-b026-0a463d2e35ba
-- title:
--   Standard Gaussian $\mu$ on $\mathbb R^N$ and normalized Hermite polynomials $H_{\mathbf m}$
-- statement:
--   Let $\mu(x)=(2\pi)^{-N/2}e^{-\|x\|^2/2}$ be the standard Gaussian density on $\mathbb R^N$; $L^2(\mu)$ has inner product $\langle g,h\rangle_\mu=\int g(x)h(x)\mu(x)\,dx$. The **normalized Hermite polynomials** are defined by
--   $$e^{zx-z^2/2}=\sum_{n=0}^\infty\frac{z^n}{\sqrt{n!}}H_n(x),$$
--   so $H_0=1$, $H_1=x$, $H_2=(x^2-1)/\sqrt2$, and in $N$ dimensions
--   $$H_{\mathbf m}(x)=\prod_{i=1}^NH_{m_i}(x_i),\qquad \mathbf m\in\mathbb Z_{\ge0}^N.$$
--   They form an orthonormal basis of $L^2(\mu)$. The **Hermite coefficient** of a function $g$ is $\langle H_{\mathbf m},g\rangle_\mu$.
--
--   **Formalization Note** $H_n=\mathrm{He}_n/\sqrt{n!}$ with $\mathrm{He}_n$ Mathlib's (probabilists') `Polynomial.hermite n`. The measure $\mu(x)\,dx$ is the product of $N$ standard normal laws. Hermite coefficients are Bochner integrals and are used only for functions known to lie in $L^2(\mu)$.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4, p. 16 and p. 17

import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4, p. 16: the standard
Gaussian density `μ(x) = (2π)^{−N/2} e^{−‖x‖²/2}` on `ℝ^N`. -/
def gaussDensity {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(N : ℝ) / 2) * Real.exp (-(∑ i, x i ^ 2) / 2)

/-- p. 17: the standard Gaussian measure `μ(x) dx` on `ℝ^N`, the product of `N` standard normal
laws; `L²(μ)` and `⟨g, h⟩_μ = ∫ g h μ dx` are taken with respect to it. -/
def gaussPi (N : ℕ) : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => gaussianReal 0 1

/-- p. 16: the normalized one-dimensional Hermite polynomial `H_n`, defined by the generating
function `e^{zx − z²/2} = Σ_n zⁿ/√n! H_n(x)`; thus `H_n = He_n / √n!` with `He_n` the
probabilists' Hermite polynomial (`H₀ = 1`, `H₁ = x`, `H₂ = (x² − 1)/√2`).

**Formalization Note.** `He_n` is Mathlib's `Polynomial.hermite n` (probabilists' convention),
evaluated at a real point. -/
def hermiteN (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.hermite n) / Real.sqrt (n.factorial : ℝ)

/-- p. 17: the multivariate Hermite polynomial `H_m(x) = Π_i H_{m_i}(x_i)` for a multi-index
`m ∈ ℤ_{≥0}^N`. These form an orthonormal basis of `L²(μ)`. -/
def hermiteMulti {N : ℕ} (m : Fin N → ℕ) (x : Fin N → ℝ) : ℝ := ∏ i, hermiteN (m i) (x i)

/-- §4.2, p. 19: the Hermite coefficient `⟨H_m, g⟩_μ = ∫ H_m(x) g(x) μ(x) dx` of a real function
`g` on `ℝ^N`.

**Formalization Note.** A Bochner integral; it is used only for functions `g` that are known to be
in `L²(μ)` (polynomials, or functions with an explicit `MemLp … 2` hypothesis), for which `H_m g`
is integrable. -/
def hermiteCoeff {N : ℕ} (g : (Fin N → ℝ) → ℝ) (m : Fin N → ℕ) : ℝ :=
  ∫ x, hermiteMulti m x * g x ∂gaussPi N

end QuadSDE


