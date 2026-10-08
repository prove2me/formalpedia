-- Prove2me | Definitions.Def_RegevLWE_GaussConv_Gaussian
-- name    : RegevLWE_GaussConv_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:59.089975+00:00
-- url     : https://prove2.me/theorems/1cf11850-5ac1-48c8-b848-807c2dfcccc0
-- title:
--   Eqs. (4)–(5) — the Gaussian function ρ_s, its shift ρ_{s,c}, the density ν_s = ρ_s/sⁿ, and the statistical distance Δ
-- statement:
--   Work in $\mathbb{R}^n$ with its Euclidean norm $\|\cdot\|$ and Lebesgue measure.
--
--   1. **Gaussian function** (Eq. (4)). For $s > 0$ and $x \in \mathbb{R}^n$,
--   $$\rho_s(x) := \exp\bigl(-\pi \|x/s\|^2\bigr) = \exp\Bigl(-\frac{\pi\|x\|^2}{s^2}\Bigr).$$
--   2. **Shifted Gaussian.** For $c \in \mathbb{R}^n$, $\rho_{s,c}(x) := \rho_s(x - c)$.
--   3. **Continuous Gaussian density** (Eq. (5)). $\nu_s := \rho_s / s^n$. Since $\int_{\mathbb{R}^n} \rho_s(x)\,dx = s^n$, $\nu_s$ is a probability density on $\mathbb{R}^n$ (the normal distribution with covariance $\frac{s^2}{2\pi} I_n$).
--   4. **Statistical distance.** For two probability densities $\varphi_1, \varphi_2$ on $\mathbb{R}^n$,
--   $$\Delta(\varphi_1, \varphi_2) := \int_{\mathbb{R}^n} |\varphi_1(x) - \varphi_2(x)|\,dx .$$
--   With this normalization (no factor $\tfrac12$) the statistical distance of two probability densities ranges in $[0, 2]$.
--
--   These are the basic objects of Regev's analysis of Gaussian measures on lattices; every statement of this mission is phrased in them.
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. The formula $\exp(-\pi\|x\|^2/s^2)$ is used for every real $s$; the paper only uses $s > 0$, and every theorem of the mission assumes it. $\Delta$ is the lower Lebesgue integral of $|\varphi_1 - \varphi_2|$ with values in $[0, \infty]$, so it cannot collapse to $0$ on a non-integrable difference (a Bochner integral would).
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:14 (statistical distance), p. 34:15, Eqs. (4), (5) and the definition of ρ_{s,c}

import Mathlib

open MeasureTheory

namespace RegevLWE.GaussConv

/-- The Gaussian function `ρ_s(x) = exp(-π ‖x / s‖²) = exp(-π ‖x‖² / s²)` on `ℝⁿ`
(Regev, J. ACM 2009, p. 34:15, Eq. (4)); the paper uses it for `s > 0`. -/
noncomputable def rho {n : ℕ} (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-Real.pi * ‖x‖ ^ 2 / s ^ 2)

/-- The shifted Gaussian `ρ_{s,c}(x) = ρ_s(x - c)` (p. 34:15). -/
noncomputable def rhoShift {n : ℕ} (s : ℝ) (c x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  rho s (x - c)

/-- The continuous Gaussian density `ν_s = ρ_s / sⁿ` on `ℝⁿ` (p. 34:15, Eq. (5)). -/
noncomputable def nu {n : ℕ} (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  rho s x / s ^ n

/-- The statistical distance `Δ(φ₁, φ₂) = ∫_{ℝⁿ} |φ₁(x) - φ₂(x)| dx` of two densities on `ℝⁿ`
(p. 34:14), with **no** factor `1/2` (its range on probability densities is `[0, 2]`).
It is a lower Lebesgue integral with values in `ℝ≥0∞`, so it never collapses to `0` on a
non-integrable difference. -/
noncomputable def statDist {n : ℕ} (φ₁ φ₂ : EuclideanSpace ℝ (Fin n) → ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal |φ₁ x - φ₂ x|

end RegevLWE.GaussConv


