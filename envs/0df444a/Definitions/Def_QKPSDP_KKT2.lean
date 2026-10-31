-- Prove2me | Definitions.Def_QKPSDP_KKT2
-- name    : QKPSDP_KKT2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:50:08.492118+00:00
-- url     : https://prove2.me/theorems/fef7e595-9f89-45cb-8d6f-29e1369de168
-- title:
--   Second-order KKT condition (33) of (SQKELR)
-- statement:
--   For $R \in \mathbb R^{n\times r}$ and multipliers $(\mu,\lambda)$, the second-order KKT condition is
--
--   $$
--   \bigl\langle -2C - 2\operatorname{diag}(\mu) - 2\lambda aa^\top,\ HH^\top \bigr\rangle \ge 0 \quad\text{for all } H \in T_R\mathcal K_{n,r}. \qquad (33)
--   $$
--
--   **Formalization Note** The page states (33) over the tangent cone and notes that under LICQ the tangent cone is the tangent space (34). The definition quantifies over (34); it is only used at regular points.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.8, proof, (33)–(34), p.14

import Mathlib
import Definitions.Def_QKPSDP_TangentSpace

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Lemma 4.8, proof, (33)–(34), p.14: the second-order KKT
condition of (SQKELR) at `R` with multipliers `(μ, λ)`,
`⟨−2C − 2diag(μ) − 2λaa⊤, HH⊤⟩ ≥ 0` for all `H ∈ T_R K_{n,r}` (the tangent space (34)).

**Formalization Note** The page states (33) over the tangent cone `T_{K_{n,r}}(R)` and says that,
because LICQ holds at `R`, it "corresponds to" the tangent space (34). The definition quantifies
over (34); it is only used together with `IsRegular`, where the two coincide. -/
def KKT2 {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (τ : ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) (μ : Fin n → ℝ) (lam : ℝ) : Prop :=
  ∀ H ∈ TangentSpace a τ R,
    0 ≤ ((-(2 : ℝ) • C - (2 : ℝ) • diagonal μ - (2 * lam) • vecMulVec a a) * (H * Hᵀ)ᵀ).trace

end QKPSDP


