-- Prove2me | Definitions.Def_OTDRO_Cvx_Domain
-- name    : OTDRO_Cvx_Domain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:22.496058+00:00
-- url     : https://prove2.me/theorems/1e7592e8-4a32-4c7b-82a6-7dce8cc15a24
-- title:
--   (11), p. 15 — the effective domain U of f_δ and the sets U₁ ⊆ U₂
-- statement:
--   Let $B \subseteq \mathbb{R}^d$ be the decision set, $\mathbb{R}_+ = [0, \infty)$, and let $f_\delta(\beta, \lambda) = E_{P_0}[\ell_{rob}(\beta, \lambda; X)]$ be the dual objective. The **effective domain** of $f_\delta$, display (11), is
--   $$\mathbb{U} := \{(\beta, \lambda) \in B \times \mathbb{R}_+ : E_{P_0}[\ell_{rob}(\beta, \lambda; X)] < \infty\}.$$
--   With the threshold $\lambda_{thr}(\beta) = \kappa\sqrt{\delta}\,\operatorname{ess\,sup}_{P_0} \beta^{\mathsf T}A(X)^{-1}\beta$, define
--   $$\mathbb{U}_1 := \{(\beta, \lambda) \in B \times \mathbb{R}_+ : \lambda > \lambda_{thr}(\beta)\}, \qquad \mathbb{U}_2 := \{(\beta, \lambda) \in B \times \mathbb{R}_+ : \lambda \ge \lambda_{thr}(\beta)\}.$$
--
--   Lemma 1 of the paper sandwiches the effective domain between these two explicit sets, $\mathbb{U}_1 \subseteq \mathbb{U} \subseteq \mathbb{U}_2$; the minimization of $f_\delta$ may be restricted to $\mathbb{U}$.
--
--   **Formalization Note** The three sets are subsets of `EuclideanSpace ℝ (Fin d) × ℝ`. Since $f_\delta$ is `EReal`-valued, "$< \infty$" is written $f_\delta(\beta, \lambda) \neq +\infty$.
-- source:
--   arXiv:1810.02403v3, §3.1, (11) and the definitions of U1, U2, p. 15

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.Cvx

open MeasureTheory

/-- The effective domain `U` of the dual objective, display (11), p. 15:
`U := {(β, λ) ∈ B × ℝ₊ : E_{P₀}[ℓ_rob(β, λ; X)] < ∞}`, with "`< ∞`" read as `≠ ⊤` in `EReal`. -/
def effDomain {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d))) (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (B : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
  {θ | θ.1 ∈ B ∧ 0 ≤ θ.2 ∧ OTDRO.Dual.fDelta P0 ℓ A δ θ.1 θ.2 ≠ ⊤}

/-- `U₁ := {(β, λ) ∈ B × ℝ₊ : λ > λ_thr(β)}`, p. 15. -/
def domU1 {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d))) (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (B : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
  {θ | θ.1 ∈ B ∧ 0 ≤ θ.2 ∧ OTDRO.Dual.lamThr P0 ℓ A δ θ.1 < θ.2}

/-- `U₂ := {(β, λ) ∈ B × ℝ₊ : λ ≥ λ_thr(β)}`, p. 15. -/
def domU2 {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d))) (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (B : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
  {θ | θ.1 ∈ B ∧ 0 ≤ θ.2 ∧ OTDRO.Dual.lamThr P0 ℓ A δ θ.1 ≤ θ.2}

end OTDRO.Cvx


