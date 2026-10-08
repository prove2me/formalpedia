-- Prove2me | Definitions.Def_SpikedWishart_FixedDim_Laguerre
-- name    : SpikedWishart_FixedDim_Laguerre
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:42.659711+00:00
-- url     : https://prove2.me/theorems/81f4d948-2521-4438-ab52-622bf599e5fe
-- title:
--   §5, p. 1691, (301)–(302) — the Laguerre eigenvalue weight V(y)²Πe^{−Mπ₁y_j}y_j^{M−k} and its normalizing constant C
-- statement:
--   Fix integers $M \ge k \ge 1$ and $\pi_1 > 0$. For $y = (y_1,\dots,y_k)\in\mathbb R^k$ the **eigenvalue weight** of (301)–(302) is
--   $$w(y) = V(y)^2\prod_{j=1}^k e^{-M\pi_1 y_j}\,y_j^{M-k},$$
--   with $V(y)^2 = \prod_{i<j}|y_i-y_j|^2$, and its **normalizing constant** is the integral over the positive orthant
--   $$C = \int_{(0,\infty)^k} w(y)\,dy_1\cdots dy_k .$$
--
--   When the covariance matrix is $\Sigma = \pi_1^{-1}I_k$, $w/C$ is the (unordered) joint density of the $k$ eigenvalues of the sample covariance matrix of $M$ complex Gaussian samples. It is a Laguerre unitary ensemble.
--
--   **Formalization Note** $C$ is defined as the integral, not by its closed form (303), which is a separate statement. The exponent $M-k$ uses natural-number subtraction; every statement using $w$ or $C$ with a finite $M$ assumes $k \le M$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1691, §5, (301)–(302)

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_GUE

namespace SpikedWishart.FixedDim

open MeasureTheory Set

/-- The unnormalized eigenvalue weight of (301)–(302):
`V(y)² Π_j e^{−Mπ₁ y_j} y_j^{M−k}` for `y ∈ ℝ^k`. -/
noncomputable def w {k : ℕ} (M : ℕ) (π₁ : ℝ) (y : Fin k → ℝ) : ℝ :=
  vandSq y * ∏ j, Real.exp (-(M : ℝ) * π₁ * y j) * (y j) ^ (M - k)

/-- The normalizing constant `C` of (301)–(302): the integral of the weight over the orthant
`(0, ∞)^k` (not its closed form (303)). -/
noncomputable def C (M k : ℕ) (π₁ : ℝ) : ℝ :=
  ∫ y in Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ)), w M π₁ y

end SpikedWishart.FixedDim


