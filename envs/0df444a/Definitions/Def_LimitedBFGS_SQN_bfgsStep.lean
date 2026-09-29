-- Prove2me | Definitions.Def_LimitedBFGS_SQN_bfgsStep
-- name    : LimitedBFGS_SQN_bfgsStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:22:08.004343+00:00
-- url     : https://prove2.me/theorems/28d57bb6-9acc-4f40-aff3-3b123f776886
-- title:
--   The BFGS update in product form $\bar H = v^T H v + \rho s s^T$ and in sum form $\bar H = H + U(s,y,H)$
-- statement:
--   Let $H$ be a real $n \times n$ matrix and let $s, y \in \mathbb{R}^n$ be a correction pair (in a minimization method, $s_k = x_{k+1} - x_k$ is the step and $y_k = g_{k+1} - g_k$ the change of gradient). Put
--
--   $$\rho = \frac{1}{y^T s}, \qquad v = I - \rho\, y s^T .$$
--
--   The **BFGS update of $H$ by $(s, y)$**, in the product form of Nocedal's equation (3), is
--
--   $$\bar H = (I - \rho s y^T)\, H\, (I - \rho y s^T) + \rho s s^T = v^T H v + \rho s s^T .$$
--
--   The same update in the sum form (1)–(2) is $\bar H = H + U(s, y, H)$ with the **BFGS correction**
--
--   $$U(s, y, H) = \frac{s s^T}{y^T s}\left[\frac{y^T H y}{y^T s} + 1\right] - \frac{1}{y^T s}\left[s y^T H + H y s^T\right].$$
--
--   This module defines $\rho$, $v$, the product-form step $H \mapsto v^T H v + \rho s s^T$ and the correction $U$. The special (limited-storage) BFGS matrices of the paper are built by applying the product-form step repeatedly to an initial matrix $H_0$; the sum form is used to state the equivalent recursion (10).
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, $x^T y$ is `dotProduct`, $s y^T$ is `Matrix.vecMulVec s y`, and $v^T$ is `Matrix.transpose`. If $y^T s = 0$, Lean's convention $1/0 = 0$ gives $\rho = 0$ and $v = I$, so the product-form step returns $H$ unchanged. This matches the paper's remark that dropping a correction is equivalent to taking $v = I$ and $\rho s s^T = 0$ (p. 774); it only happens for the zero pair stored after an iteration has already reached the minimizer.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 774, eqs. (1)–(3); p. 775, definitions of ρ_i and v_i. DOI 10.1090/s0025-5718-1980-0572855-7

import Mathlib

open Matrix

namespace LimitedBFGS.SQN

/-- `ρ = 1 / yᵀs` (Nocedal 1980, p. 774, below (3); p. 775, `ρ_i = 1/y_iᵀs_i`).
If `yᵀs = 0` then Lean's `1 / 0 = 0` gives `ρ = 0`. -/
noncomputable def bfgsRho {n : ℕ} (s y : Fin n → ℝ) : ℝ :=
  1 / (y ⬝ᵥ s)

/-- `v = I − ρ y sᵀ` (Nocedal 1980, p. 775, `v_i = (I − ρ_i y_i s_iᵀ)`). -/
noncomputable def bfgsV {n : ℕ} (s y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - bfgsRho s y • vecMulVec y s

/-- The BFGS update of `H` by the pair `(s, y)` in product form (3), p. 774:
`H̄ = (I − ρ s yᵀ) H (I − ρ y sᵀ) + ρ s sᵀ = vᵀ H v + ρ s sᵀ`.
When `yᵀs = 0`, `ρ = 0` and `v = I`, so the step returns `H` unchanged: this is the paper's
"dropping a correction is equivalent to defining `v = I` and `ρssᵀ = 0`" (p. 774). -/
noncomputable def bfgsStep {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (bfgsV s y)ᵀ * H * bfgsV s y + bfgsRho s y • vecMulVec s s

/-- The BFGS correction `U(s, y, H)` of the sum form (1)–(2), p. 774:
`U(s, y, H) = (s sᵀ / yᵀs) [yᵀHy / yᵀs + 1] − (1 / yᵀs) [s yᵀ H + H y sᵀ]`,
so that the BFGS update is `H̄ = H + U(s, y, H)`. -/
noncomputable def bfgsU {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (((y ⬝ᵥ (H *ᵥ y)) / (y ⬝ᵥ s) + 1) / (y ⬝ᵥ s)) • vecMulVec s s
    - (1 / (y ⬝ᵥ s)) • (vecMulVec s y * H + H * vecMulVec y s)

end LimitedBFGS.SQN


