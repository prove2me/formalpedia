-- Prove2me | Definitions.Def_QKPSDP_KKT1
-- name    : QKPSDP_KKT1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:08.110013+00:00
-- url     : https://prove2.me/theorems/03d5a4b4-1d29-4515-83fa-a82cbaa43b79
-- title:
--   First-order KKT equation (32) of (SQKELR)
-- statement:
--   For $R \in \mathbb R^{n\times r}$ and multipliers $(\mu,\lambda) \in \mathbb R^n \times \mathbb R$, the first-order KKT equation of (SQKELR) is
--
--   $$
--   -2CR - 2\operatorname{diag}(\mu)R + \mu e_1^\top - 2\lambda aa^\top R + \lambda\tau\, a e_1^\top = 0. \qquad (32)
--   $$
--
--   It is stationarity of the Lagrangian of (SQKELR) with multiplier $\mu_i$ for the $i$-th constraint of $\operatorname{diag}(RR^\top) = Re_1$ and $\lambda$ for $\|a^\top R\|^2 - \tau a^\top Re_1 = 0$.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.8, proof, (32), p.14

import Mathlib
import Definitions.Def_QKPSDP_e1

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Lemma 4.8, proof, (32), p.14: the first-order KKT equation of
(SQKELR) at `R` with multipliers `(μ, λ) ∈ ℝⁿ × ℝ`,
`−2CR − 2diag(μ)R + μe₁⊤ − 2λaa⊤R + λτae₁⊤ = 0`.

**Formalization Note** `λ` is `lam`; `diag(μ)` is `diagonal μ`; `μe₁⊤`, `aa⊤`, `ae₁⊤` are
`vecMulVec`. Signs and the factors 2 are those of the page. -/
def KKT1 {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (τ : ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) (μ : Fin n → ℝ) (lam : ℝ) : Prop :=
  -(2 : ℝ) • (C * R) - (2 : ℝ) • (diagonal μ * R) + vecMulVec μ (e1 r)
      - (2 * lam) • (vecMulVec a a * R) + (lam * τ) • vecMulVec a (e1 r) = 0

end QKPSDP


