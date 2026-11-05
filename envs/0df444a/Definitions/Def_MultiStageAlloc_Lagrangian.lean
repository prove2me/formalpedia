-- Prove2me | Definitions.Def_MultiStageAlloc_Lagrangian
-- name    : MultiStageAlloc_Lagrangian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:35.14988+00:00
-- url     : https://prove2.me/theorems/058c12c8-63de-474b-82ca-0c516de05049
-- title:
--   The Lagrangian $\mathcal L_k$ of the stage program (Definition 2)
-- statement:
--   Given levels $y$, the Lagrangian of the stage program with multipliers $\lambda,\theta,\gamma$ is
--   $$
--   \mathcal L_k(x,\lambda,\theta,\gamma)=\sum_{j\in V}\Bigl(w_j\sum_i x_{ij}-n_jw_j\tilde F_k\bigl(y_j+\sum_i \tfrac{x_{ij}}{n_j}\bigr)\Bigr)-\sum_{i\in U_k}\lambda_i\Bigl(\sum_j x_{ij}-1\Bigr)-\sum_{j\in V}\theta_j\Bigl(y_j+\sum_i \tfrac{x_{ij}}{n_j}-1\Bigr)+\sum_{(i,j)\in E_k}\gamma_{ij}x_{ij}.
--   $$
--   The multipliers are **dual feasible** when $\lambda_i\ge 0$ on $U_k$, $\theta_j\ge 0$ on $V$ and $\gamma_{ij}\ge 0$ on $E_k$. It is the function in the KKT statement of Proposition 3.
--
--   **Formalization Note** At $n\equiv 1$ this is the printed $\mathcal L_k$ with the $C^1$ extension $\tilde F_k$ in place of $F_k$; the two agree on $[0,1]$. Here $\theta_j$ dualizes the constraint in level units.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Definition 2, p.39

import Mathlib
import Definitions.Def_MultiStageAlloc_StageProgram

namespace MultiStageAlloc

variable {U V : Type*} [Fintype U] [Fintype V] {K : ℕ}

/-- **Dual feasibility of the multipliers of (P^VWM_k)**, arXiv:2211.16581v1, Proposition 3, p.39:
`λ_i ≥ 0` for `i ∈ U_k`, `θ_j ≥ 0` for `j ∈ V`, and `γ_ij ≥ 0` for `(i, j) ∈ E_k`. Values of `lam`
off `U_k` and of `γ` off `E_k` do not enter the Lagrangian on stage-`k` allocations. -/
def DualNonneg (I : Instance U V K) (k : ℕ) (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ) : Prop :=
  (∀ i, I.batch i = k → 0 ≤ lam i) ∧ (∀ j, 0 ≤ θ j) ∧
    ∀ i j, I.edge i j → I.batch i = k → 0 ≤ γ i j

/-- **The Lagrangian `L_k(x, λ, θ, γ)` of (P^VWM_k)**, arXiv:2211.16581v1, Definition 2, p.39, given
the levels `y`:
`∑_j (w_j ∑_i x_ij - n_j w_j F̃_k(y_j + ∑_i x_ij / n_j)) - ∑_{i ∈ U_k} λ_i (∑_j x_ij - 1)
  - ∑_j θ_j (y_j + ∑_i x_ij / n_j - 1) + ∑ γ_ij x_ij`.

**Formalization Note.** At `n_j = 1` this is the printed `L_k` with `F̃_k` in place of `F_k`. Here
`F̃_k` (`regFext`) equals `F_k` on `[0, 1]`; the page takes `x` with no sign constraint, which leaves
`F_k`'s domain, so the extension is what gives the printed `max_x` a meaning. -/
noncomputable def lagrangian (I : Instance U V K) (k : ℕ) (y : V → ℝ) (x : U → V → ℝ)
    (lam : U → ℝ) (θ : V → ℝ) (γ : U → V → ℝ) : ℝ :=
  ∑ j, (I.w j * ∑ i, x i j - I.cap j * I.w j * regFext K k (level I y x j))
    - ∑ i with I.batch i = k, lam i * (∑ j, x i j - 1)
    - ∑ j, θ j * (level I y x j - 1)
    + ∑ i, ∑ j, γ i j * x i j

end MultiStageAlloc


