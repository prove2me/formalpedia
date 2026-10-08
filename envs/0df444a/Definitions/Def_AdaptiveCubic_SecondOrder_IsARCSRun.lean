-- Prove2me | Definitions.Def_AdaptiveCubic_SecondOrder_IsARCSRun
-- name    : AdaptiveCubic_SecondOrder_IsARCSRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:28.570083+00:00
-- url     : https://prove2.me/theorems/b7bb01ed-d015-4019-b5a0-d3adae291e83
-- title:
--   A run of Algorithm 4.1, ARC(S)
-- statement:
--   A run of **ARC(S)** is a run of ARC (Algorithm 2.1, so the Cauchy condition (2.2) remains satisfied) in which every step $s_k$ also satisfies
--
--   $$g_k^\top s_k + s_k^\top B_k s_k + \sigma_k\|s_k\|^3 = 0, \qquad (4.1)$$
--
--   $$s_k^\top B_k s_k + \sigma_k\|s_k\|^3 \ge 0, \qquad (4.2)$$
--
--   and the termination criterion **TC.s** (4.7):
--
--   $$\|\nabla_s m_k(s_k)\| \le \theta_k\|g_k\|, \qquad \theta_k=\kappa_\theta\min(1,\|s_k\|),$$
--
--   for a fixed constant $\kappa_\theta\in(0,1)$, where $\nabla_s m_k(s)=g_k+B_ks+\sigma_k\|s\|\,s$.
--
--   Conditions (4.1)–(4.2) hold for any global minimizer of the model over a subspace, and TC.s stops the inner minimization once the model gradient is small relative to $g_k$.
--
--   **Formalization Note** TC.s is stated with the explicit model gradient $g_k+B_ks_k+\sigma_k\|s_k\|s_k$ given on p. 13 of the paper.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 10, (4.1)–(4.2); p. 11, TC.s (4.7); p. 12, Algorithm 4.1; p. 13 (model gradient)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- A run of Algorithm 4.1, ARC(S), p. 12, of Cartis, Gould & Toint, *Adaptive cubic regularisation
methods for unconstrained optimization. Part II*, preprint rev. 15 Sep 2009: a run of ARC
(Algorithm 2.1, `IsARCRun`, so (2.2) remains satisfied) in which every step `s_k` also satisfies
* (4.1), p. 10: `g_kᵀ s_k + s_kᵀ B_k s_k + σ_k ‖s_k‖³ = 0`;
* (4.2), p. 10: `s_kᵀ B_k s_k + σ_k ‖s_k‖³ ≥ 0`;
* TC.s (4.7), p. 11: `‖∇_s m_k(s_k)‖ ≤ θ_k ‖g_k‖` with `θ_k = κ_θ min(1, ‖s_k‖)` and a constant
  `κ_θ ∈ (0, 1)`, where `∇_s m_k(s) = g_k + B_k s + σ_k ‖s‖ s` (p. 13). -/
def IsARCSRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B ∧ 0 < κθ ∧ κθ < 1 ∧
  ∀ k,
    ⟪gradient f (x k), s k⟫ + ⟪s k, B k (s k)⟫ + σ k * ‖s k‖ ^ 3 = 0 ∧
    0 ≤ ⟪s k, B k (s k)⟫ + σ k * ‖s k‖ ^ 3 ∧
    ‖gradient f (x k) + B k (s k) + (σ k * ‖s k‖) • s k‖ ≤
      κθ * min 1 ‖s k‖ * ‖gradient f (x k)‖

end AdaptiveCubic.SecondOrder


