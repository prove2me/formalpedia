-- Prove2me | Definitions.Def_EntropicBarrier_Universal_ExpFamily
-- name    : EntropicBarrier_Universal_ExpFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:02:37.028177+00:00
-- url     : https://prove2.me/theorems/81616e61-ba15-400b-9d57-3a7ad4d58a82
-- title:
--   Canonical exponential family $p_\theta$, mean $x(\theta)$, covariance $\Sigma(\theta)$ and third moment $T(\theta)$
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ and let $f$ be its log-Laplace transform. For $\theta\in\mathbb R^n$, $p_\theta$ is the measure on $\mathbb R^n$ with Lebesgue density
--   $$\exp(\langle\theta,x\rangle-f(\theta))\,\mathbb 1\{x\in\mathcal K\},$$
--   a probability measure when $\mathcal K$ is a convex body. Its mean, covariance and third central moment are
--   $$x(\theta)=\mathbb E_{X\sim p_\theta}X,\qquad \Sigma(\theta)=\mathbb E_{X\sim p_\theta}(X-x(\theta))(X-x(\theta))^\top,$$
--   $$T(\theta)=\mathbb E_{X\sim p_\theta}(X-x(\theta))\otimes(X-x(\theta))\otimes(X-x(\theta)).$$
--
--   The family $\{p_\theta\}$ is the canonical exponential family of $\mathcal K$, with $f$ as its log-partition function; it connects the derivatives of $f$ and $f^*$ with moments of $p_\theta$.
--
--   **Formalization Note** $\Sigma(\theta)$ is represented twice: as the bilinear form `covForm K θ h k` $=\mathbb E\langle X-x(\theta),h\rangle\langle X-x(\theta),k\rangle$, and as the vector `covApply K θ h` $=\Sigma(\theta)h=\mathbb E\langle X-x(\theta),h\rangle(X-x(\theta))$; $T(\theta)$ is the trilinear form `thirdMomentForm`. For a convex body all integrands are continuous on the compact support of the finite measure $p_\theta$, hence integrable, so the Bochner integrals are the true expectations.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 5, §3

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

/-- The **canonical exponential family** of `K` (§3, p. 5): `p_θ` has Lebesgue density
`exp(⟪θ, x⟫ - f(θ)) 𝟙{x ∈ K}`. -/
noncomputable def expFamily {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume.restrict K).withDensity
    (fun x => ENNReal.ofReal (Real.exp (⟪θ, x⟫ - logPartition K θ)))

/-- The mean `x(θ) = 𝔼_{X ∼ p_θ} X` (§3, p. 5). -/
noncomputable def meanMap {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∫ x, x ∂(expFamily K θ)

/-- The covariance `Σ(θ) = 𝔼_{X ∼ p_θ} (X - x(θ))(X - x(θ))ᵀ` (§3, p. 5), as the bilinear
form `(h, k) ↦ 𝔼 ⟪X - x(θ), h⟫ ⟪X - x(θ), k⟫`. -/
noncomputable def covForm {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ h k : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x, ⟪x - meanMap K θ, h⟫ * ⟪x - meanMap K θ, k⟫ ∂(expFamily K θ)

/-- The covariance `Σ(θ)` applied to a vector: `Σ(θ) h = 𝔼 ⟪X - x(θ), h⟫ (X - x(θ))`. -/
noncomputable def covApply {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ h : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∫ x, ⟪x - meanMap K θ, h⟫ • (x - meanMap K θ) ∂(expFamily K θ)

/-- The third central moment tensor `T(θ) = 𝔼 (X - x(θ)) ⊗ (X - x(θ)) ⊗ (X - x(θ))`
(§3, p. 5), as a trilinear form. -/
noncomputable def thirdMomentForm {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ h₁ h₂ h₃ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x, ⟪x - meanMap K θ, h₁⟫ * ⟪x - meanMap K θ, h₂⟫ * ⟪x - meanMap K θ, h₃⟫
    ∂(expFamily K θ)

end EntropicBarrier.Universal


