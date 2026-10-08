-- Prove2me | Definitions.Def_SpikedWishart_FixedDim_GUE
-- name    : SpikedWishart_FixedDim_GUE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:48:46.56367+00:00
-- url     : https://prove2.me/theorems/3fb8cafc-1b59-4bbd-b0c7-4aeb587da268
-- title:
--   §1.2.2, pp. 1648–1649, (26)–(28) — Vandermonde weight, Selberg constant Z_k and the finite-GUE distribution G_k
-- statement:
--   For $k \ge 1$ and $\xi = (\xi_1,\dots,\xi_k)\in\mathbb R^k$ write
--   $$V(\xi)^2 = \prod_{1\le i<j\le k}|\xi_i-\xi_j|^2$$
--   for the squared Vandermonde product. The **normalization constant** of (27) is the integral
--   $$Z_k = \int_{\mathbb R^k} V(\xi)^2\prod_{i=1}^k e^{-\frac12\xi_i^2}\,d\xi_1\cdots d\xi_k,$$
--   and the **finite-GUE distribution** of Definition 1.2, (28), is
--   $$G_k(x) = \frac1{Z_k}\int_{-\infty}^x\!\!\cdots\int_{-\infty}^x V(\xi)^2\prod_{i=1}^k e^{-\frac12\xi_i^2}\,d\xi_1\cdots d\xi_k,\qquad x\in\mathbb R.$$
--
--   $G_k$ is the distribution function of the largest eigenvalue of a $k\times k$ matrix from the Gaussian unitary ensemble with joint eigenvalue density (26). It is the limit law of the largest sample eigenvalue in Proposition 1.1 of the paper, and of the separated spikes in Theorem 1.1(b).
--
--   **Formalization Note** $Z_k$ is defined as the integral, not by its closed form $(2\pi)^{k/2}\prod_{j=1}^k j!$; that closed form is the separate statement (27). The integrand is integrable, so $Z_k > 0$ and the division in $G_k$ is genuine.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1648–1649, §1.2.2, (26)–(28), Definition 1.2

import Mathlib

namespace SpikedWishart.FixedDim

open MeasureTheory Set

/-- The squared Vandermonde product `Π_{1≤i<j≤k} |ξ_i − ξ_j|²`. -/
noncomputable def vandSq {k : ℕ} (ξ : Fin k → ℝ) : ℝ :=
  ∏ i, ∏ j, if i < j then (ξ i - ξ j) ^ 2 else 1

/-- The normalization constant `Z_k` of (27), as the integral (not its closed form). -/
noncomputable def Z (k : ℕ) : ℝ :=
  ∫ ξ : Fin k → ℝ, vandSq ξ * ∏ i, Real.exp (-(ξ i) ^ 2 / 2)

/-- The finite-GUE distribution function `G_k(x)` of Definition 1.2, (28). -/
noncomputable def G (k : ℕ) (x : ℝ) : ℝ :=
  (Z k)⁻¹ * ∫ ξ in Set.pi univ (fun _ : Fin k => Iic x), vandSq ξ * ∏ i, Real.exp (-(ξ i) ^ 2 / 2)

end SpikedWishart.FixedDim


