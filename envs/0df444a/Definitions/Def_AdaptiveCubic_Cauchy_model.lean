-- Prove2me | Definitions.Def_AdaptiveCubic_Cauchy_model
-- name    : AdaptiveCubic_Cauchy_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:49.568753+00:00
-- url     : https://prove2.me/theorems/ac375da2-50d8-495c-ac2a-a979761a9436
-- title:
--   The cubic model $m_k$ (1.2) and the ratio $\rho_k$ (2.4)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, let $g(x)=\nabla f(x)$ be its gradient and let $\|\cdot\|$ be the Euclidean norm. At an iterate $x_k$, with a symmetric matrix $B_k$ (an approximation of the Hessian) and a regularisation weight $\sigma_k$, the **cubic model** of the adaptive cubic regularisation (ARC) method is
--
--   $$
--   m_k(s)=f(x_k)+s^{T}g_k+\tfrac12\, s^{T}B_k s+\tfrac13\,\sigma_k\|s\|^3,\qquad s\in\mathbb R^n,
--   $$
--
--   where $g_k=g(x_k)$. Given a trial step $s_k$, the **ratio of actual to predicted decrease** is
--
--   $$
--   \rho_k=\frac{f(x_k)-f(x_k+s_k)}{f(x_k)-m_k(s_k)} .
--   $$
--
--   The model is the second-order Taylor model of $f$ at $x_k$ (with $B_k$ in place of the Hessian) plus a cubic regulariser whose weight $\sigma_k$ is adapted from iteration to iteration; $\rho_k$ decides whether the step is accepted and how $\sigma_k$ is updated.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`, $g$ is Mathlib's `gradient f` and $B_k$ is a continuous linear operator. The cubic coefficient is $\sigma_k/3$, as printed. Lean's real division returns $0$ when the denominator vanishes, so an iteration with $m_k(s_k)=f(x_k)$ gets $\rho_k=0$; the paper assumes $m_k(s_k)<f(x_k)$ (2.6) whenever the algorithm has not terminated, and every theorem of this mission either assumes (2.6) or works only on iterations with $g_k\neq0$, where the Cauchy condition makes the denominator positive.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 2, (1.2); p. 4, (2.4)

import Mathlib

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- The cubic model (1.2) of Cartis, Gould & Toint, *Adaptive cubic regularisation methods for
unconstrained optimization. Part II*, preprint rev. 15 Sep 2009, p. 2:
`m_k(s) = f(x_k) + sᵀ g_k + ½ sᵀ B_k s + (1/3) σ_k ‖s‖³`,
where `g_k = ∇f(x_k)` is `gradient f x`, `B_k` is the operator `B` (a symmetric approximation of the
Hessian), `σ_k` is `σ`, and `‖·‖` is the Euclidean norm of `ℝⁿ = EuclideanSpace ℝ (Fin n)`. -/
noncomputable def model {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (σ : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + ⟪s, gradient f x⟫ + 1 / 2 * ⟪s, B s⟫ + σ / 3 * ‖s‖ ^ 3

/-- The ratio (2.4), p. 4, of actual to predicted decrease:
`ρ_k = (f(x_k) − f(x_k + s_k)) / (f(x_k) − m_k(s_k))`.
Lean's real division returns `0` when the denominator is `0`, so such an iteration counts as
unsuccessful. Every theorem of this mission that uses `ρ_k` either assumes (2.6),
`m_k(s_k) < f(x_k)`, or concerns iterations with `g_k ≠ 0`, where the Cauchy condition (2.2) makes
the denominator positive (Lemma 3.1 i)). -/
noncomputable def rho {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (σ : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (f x - f (x + s)) / (f x - model f B σ x s)

end AdaptiveCubic.Cauchy


