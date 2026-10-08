-- Prove2me | Definitions.Def_AdaptiveCubic_FirstOrder_IsARCSRun
-- name    : AdaptiveCubic_FirstOrder_IsARCSRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:13.83218+00:00
-- url     : https://prove2.me/theorems/03c91056-0028-4481-a449-7739d40a9829
-- title:
--   The termination rule TC.s (4.7) and a run of Algorithm 4.1, ARC(S)
-- statement:
--   Fix a constant $\kappa_\theta\in(0,1)$. The **termination criterion TC.s** (4.7) requires, for every $k$,
--
--   $$\|\nabla_s m_k(s_k)\|\le\theta_k\|g_k\|,\qquad \theta_k=\kappa_\theta\min(1,\|s_k\|),$$
--
--   where $\nabla_s m_k(s)=g_k+B_k s+\sigma_k\|s\|\,s$ is the gradient of the cubic model.
--
--   A **run of ARC(S)** (Algorithm 4.1) is a run of ARC (Algorithm 2.1, so the Cauchy condition (2.2) remains satisfied) in which every step $s_k$ also satisfies
--
--   1. (4.1) $\;g_k^\top s_k+s_k^\top B_k s_k+\sigma_k\|s_k\|^3=0$;
--   2. (4.2) $\;s_k^\top B_k s_k+\sigma_k\|s_k\|^3\ge0$;
--   3. TC.s (4.7).
--
--   Conditions (4.1)–(4.2) hold whenever $s_k$ globally minimizes $m_k$ over a subspace containing it; TC.s keeps the step from being too short relative to the gradient. ARC(S) is the second-order variant of ARC whose complexity is analysed in §5.
--
--   **Formalization Note** The model gradient in TC.s is written out explicitly as $g_k+B_ks_k+\sigma_k\|s_k\|s_k$ (the formula on p. 13) rather than as a Fréchet derivative. TC.s is its own definition `TCs` because Lemma 5.2 assumes TC.s without (4.1)–(4.2).
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 10, (4.1)–(4.2); p. 11, (4.7); p. 12, Algorithm 4.1; p. 13, formula for ∇_s m_k

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

/-- The termination criterion TC.s (4.7), p. 11, of Cartis, Gould & Toint, *Adaptive cubic
regularisation methods for unconstrained optimization. Part II*, preprint rev. 15 Sep 2009: for
every `k`, `‖∇_s m_k(s_k)‖ ≤ θ_k ‖g_k‖` with `θ_k = κ_θ min(1, ‖s_k‖)`, for a constant
`κ_θ ∈ (0, 1)`. The AdaptiveCubic.Cauchy.model gradient is written out as `∇_s m_k(s) = g_k + B_k s + σ_k ‖s‖ s` (p. 13). -/
def TCs {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (κθ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  0 < κθ ∧ κθ < 1 ∧
  ∀ k, ‖gradient f (x k) + B k (s k) + (σ k * ‖s k‖) • s k‖ ≤
      κθ * min 1 ‖s k‖ * ‖gradient f (x k)‖

/-- A run of Algorithm 4.1, ARC(S), p. 12: a run of ARC (Algorithm 2.1, `IsARCRun`, so the Cauchy
condition (2.2) remains satisfied) in which every step `s_k` also satisfies
* (4.1), p. 10: `g_kᵀ s_k + s_kᵀ B_k s_k + σ_k ‖s_k‖³ = 0`;
* (4.2), p. 10: `s_kᵀ B_k s_k + σ_k ‖s_k‖³ ≥ 0`;
* TC.s (4.7), p. 11 (`TCs`), with constant `κ_θ ∈ (0, 1)`. -/
def IsARCSRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B ∧ TCs f κθ x s σ B ∧
  ∀ k,
    ⟪gradient f (x k), s k⟫ + ⟪s k, B k (s k)⟫ + σ k * ‖s k‖ ^ 3 = 0 ∧
    0 ≤ ⟪s k, B k (s k)⟫ + σ k * ‖s k‖ ^ 3

end AdaptiveCubic.FirstOrder


