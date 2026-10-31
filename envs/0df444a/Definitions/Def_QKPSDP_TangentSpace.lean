-- Prove2me | Definitions.Def_QKPSDP_TangentSpace
-- name    : QKPSDP_TangentSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:08.638994+00:00
-- url     : https://prove2.me/theorems/3e9594d7-1cb4-4200-a98d-3f65089a25c4
-- title:
--   The tangent space (34) of $\mathcal K_{n,r}$
-- statement:
--   $$
--   T_R\mathcal K_{n,r} := \bigl\{ H \in \mathbb R^{n\times r} : 2\langle aa^\top R, H\rangle - \tau a^\top H e_1 = 0,\ 2\operatorname{diag}(RH^\top) - He_1 = 0 \bigr\}. \qquad (34)
--   $$
--
--   It is the kernel of the derivative of the constraints of (1) at $R$; at a regular point it is the tangent cone of $\mathcal K_{n,r}$.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (34), p.14

import Mathlib
import Definitions.Def_QKPSDP_e1

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (34), p.14: the tangent space of `K_{n,r}` at `R`,
`T_R K_{n,r} := { H ∈ ℝ^{n×r} : 2⟨aa⊤R, H⟩ − τa⊤He₁ = 0, 2diag(RH⊤) − He₁ = 0 }`.

**Formalization Note** `⟨A, B⟩ = Tr(AB⊤)`, so `⟨aa⊤R, H⟩` is `(vecMulVec a a * R * Hᵀ).trace`.
The page writes the bound variable as `h` and the conditions with `H`; they are the same variable. -/
def TangentSpace {n r : ℕ} [NeZero r] (a : Fin n → ℝ) (τ : ℝ) (R : Matrix (Fin n) (Fin r) ℝ) :
    Set (Matrix (Fin n) (Fin r) ℝ) :=
  {H | 2 * (vecMulVec a a * R * Hᵀ).trace - τ * (a ⬝ᵥ (H *ᵥ e1 r)) = 0 ∧
    (2 : ℝ) • (R * Hᵀ).diag - H *ᵥ e1 r = 0}

end QKPSDP


