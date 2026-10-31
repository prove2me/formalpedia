-- Prove2me | Definitions.Def_QKPSDP_IsRegular
-- name    : QKPSDP_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:55.354874+00:00
-- url     : https://prove2.me/theorems/a8ca698a-5602-4279-bbc4-138a81c8c382
-- title:
--   Regular (LICQ) points of $\mathcal K_{n,r}$
-- statement:
--   A point $R \in \mathcal K_{n,r}$ is **regular** if the linear independence constraint qualification (LICQ) holds at $R$; otherwise it is **non-regular**. The gradients of the $n+1$ constraints of (1) at $R$ are the matrices $e_ie_i^\top(2R - ee_1^\top)$, $i \in [n]$, and $a(2a^\top R - \tau e_1^\top)$, so $R$ is regular exactly when the equation
--
--   $$
--   \operatorname{diag}(\mu)\,(2R - ee_1^\top) + \lambda\, a\,(2a^\top R - \tau e_1^\top) = 0 \qquad (5)
--   $$
--
--   in $(\mu,\lambda) \in \mathbb R^n \times \mathbb R$ has only the solution $\mu = 0$, $\lambda = 0$.
--
--   Classical first- and second-order optimality conditions apply at regular points; the paper's main theorem also covers non-regular ones.
--
--   **Formalization Note** Regularity is encoded through (5); it does not involve the cost matrix $C$.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, §3.1, p.6, and (5), p.7

import Mathlib
import Definitions.Def_QKPSDP_e1

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, §3.1, p.6, with (5), p.7: "a point `R ∈ K_{n,r}` is regular if
the linear independent constraint qualification (LICQ) holds at `R`". The `n + 1` constraint
gradients of (1) at `R` are `eᵢeᵢ⊤(2R − ee₁⊤)` (`i ∈ [n]`) and `a(2a⊤R − τe₁⊤)`, so LICQ fails
exactly when some nonzero `(μ, λ) ∈ ℝⁿ × ℝ` solves (5):
`diag(μ)(2R − ee₁⊤) + λa(2a⊤R − τe₁⊤) = 0`.

**Formalization Note** Regularity is encoded as "(5) has only the trivial solution `μ = 0`,
`λ = 0`", which is linear independence of the `n + 1` gradient matrices. `λ` is written `lam`
(a Lean keyword). `ee₁⊤` is `vecMulVec 1 e₁` with `1` the all-ones vector `e`; `a(⋯)` is
`vecMulVec a (⋯)`. The predicate does not involve `C`; it is applied to points of `K_{n,r}`. -/
def IsRegular {n r : ℕ} [NeZero r] (a : Fin n → ℝ) (τ : ℝ) (R : Matrix (Fin n) (Fin r) ℝ) :
    Prop :=
  ∀ (μ : Fin n → ℝ) (lam : ℝ),
    diagonal μ * ((2 : ℝ) • R - vecMulVec (fun _ => (1 : ℝ)) (e1 r)) +
        lam • vecMulVec a ((2 : ℝ) • (a ᵥ* R) - τ • e1 r) = 0 →
      μ = 0 ∧ lam = 0

end QKPSDP


