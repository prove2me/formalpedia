-- Prove2me | Definitions.Def_RISRO_blockForm
-- name    : RISRO_blockForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:53.787992+00:00
-- url     : https://prove2.me/theorems/04d8ac75-f310-49a2-b04e-875459c46f28
-- title:
--   Block product $[U\ U_\perp][\cdot][V\ V_\perp]^\top$
-- statement:
--   For blocks $M\in\mathbb R^{r\times r}$, $N_2\in\mathbb R^{r\times(p_2-r)}$, $N_1\in\mathbb R^{(p_1-r)\times r}$, $K\in\mathbb R^{(p_1-r)\times(p_2-r)}$,
--
--   $$
--   [U\ U_\perp]\begin{bmatrix} M & N_2\\ N_1 & K\end{bmatrix}[V\ V_\perp]^\top=UMV^\top+UN_2V_\perp^\top+U_\perp N_1V^\top+U_\perp KV_\perp^\top .
--   $$
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, proof of Theorem 1, Step 4, p.40

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The block product `[U U_⊥] [M N₂; N₁ K] [V V_⊥]ᵀ`, written out as
`U M Vᵀ + U N₂ V_⊥ᵀ + U_⊥ N₁ Vᵀ + U_⊥ K V_⊥ᵀ`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, proof of Theorem 1, Step 4, p.40. -/
def blockForm {p₁ p₂ r : ℕ} (U : Matrix (Fin p₁) (Fin r) ℝ)
    (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ) (V : Matrix (Fin p₂) (Fin r) ℝ)
    (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ) (M : Matrix (Fin r) (Fin r) ℝ)
    (N₂ : Matrix (Fin r) (Fin (p₂ - r)) ℝ) (N₁ : Matrix (Fin (p₁ - r)) (Fin r) ℝ)
    (K : Matrix (Fin (p₁ - r)) (Fin (p₂ - r)) ℝ) : Matrix (Fin p₁) (Fin p₂) ℝ :=
  U * M * Vᵀ + U * N₂ * Vcᵀ + Uc * N₁ * Vᵀ + Uc * K * Vcᵀ

end RISRO


