-- Prove2me | Definitions.Def_DLT_GaussianIntegrals
-- name    : DLT_GaussianIntegrals
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T21:14:56.866115+00:00
-- url     : https://prove2.me/theorems/0f7b1b8e-bd1c-4481-966f-d1788f8e38c0
-- title:
--   Multivariable Gaussian density, Gaussian expectation, and pairings
-- statement:
--   Definitions for §1.1 of *The Principles of Deep Learning Theory*.
--
--   Let $K$ be a real $N\times N$ matrix with inverse $K^{-1}$ (written $K^{\mu\nu}$).
--
--   1. The **quadratic form** $Q_K(z) = \sum_{\mu,\nu} z_\mu (K^{-1})_{\mu\nu} z_\nu$ for $z\in\mathbb{R}^N$ (eq. 1.28).
--   2. The **zero-mean Gaussian density** with covariance $K$ (eq. 1.31):
--   $$p_K(z) = \frac{1}{\sqrt{(2\pi)^N \det K}}\, e^{-\frac12 Q_K(z)}.$$
--   3. The **Gaussian expectation** of an observable $F:\mathbb{R}^N\to\mathbb{R}$ (eqs. 1.36, 1.46):
--   $$\mathbb{E}_K[F] = \int_{\mathbb{R}^N} p_K(z)\,F(z)\,d^N z.$$
--   4. The set of **pairings** of $M$ labels: permutations $\sigma$ of $\{0,\dots,M-1\}$ with $\sigma\circ\sigma = \mathrm{id}$ and no fixed point; $\sigma$ pairs each label $a$ with $\sigma(a)$.
--
--   These are the objects in which Wick's theorem (eq. 1.45) and its special cases are stated.
--
--   **Formalization Note** Vectors are functions `Fin N → ℝ` integrated against Lebesgue measure. The definitions make sense for any matrix; the theorems of the mission assume $K$ positive definite, as in the book.
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §1.1, pp. 19–22, eqs. (1.28), (1.31), (1.36), (1.45), (1.46) (page numbers are the book's printed page numbers)

import Mathlib

/-!
# The Principles of Deep Learning Theory — Gaussian integrals (§1.1)

Zero-mean multivariable Gaussian distribution with covariance `K` (eq. 1.31/1.34),
Gaussian expectations (eq. 1.36), and the set of pairings used in Wick's theorem (eq. 1.45).
-/

open MeasureTheory

namespace DeepLearningTheory

/-- The Gaussian quadratic form `∑_{μ,ν} z_μ (K⁻¹)_{μν} z_ν` (eq. 1.28). -/
noncomputable def gaussQuadForm {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (z : Fin N → ℝ) : ℝ :=
  ∑ μ : Fin N, ∑ ν : Fin N, z μ * K⁻¹ μ ν * z ν

/-- Zero-mean multivariable Gaussian density with covariance `K` (eq. 1.31):
`p(z) = |2πK|^{-1/2} exp(-½ ∑ z_μ (K⁻¹)_{μν} z_ν)`, where `|2πK| = det(2πK) = (2π)^N det K`. -/
noncomputable def gaussianDensity {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (z : Fin N → ℝ) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ N * K.det))⁻¹ * Real.exp (-(1 / 2) * gaussQuadForm K z)

/-- Expectation `E[F(z)] = ∫ dᴺz p(z) F(z)` under the zero-mean Gaussian with covariance `K`
(eqs. 1.36, 1.46), with respect to Lebesgue measure on `ℝᴺ`. -/
noncomputable def gaussExpect {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (F : (Fin N → ℝ) → ℝ) : ℝ :=
  ∫ z, gaussianDensity K z * F z

/-- The pairings of `M` labels: fixed-point-free involutions of `{0, …, M-1}`.
A pairing `σ` pairs each label `a` with `σ a`. -/
def pairings (M : ℕ) : Finset (Equiv.Perm (Fin M)) :=
  Finset.univ.filter (fun σ => σ * σ = 1 ∧ ∀ a, σ a ≠ a)

end DeepLearningTheory


