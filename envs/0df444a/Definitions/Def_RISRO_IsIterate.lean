-- Prove2me | Definitions.Def_RISRO_IsIterate
-- name    : RISRO_IsIterate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:32:00.916529+00:00
-- url     : https://prove2.me/theorems/eaca2923-9533-4344-83d5-08b2302d0c2b
-- title:
--   The data of the $t$-th iteration
-- statement:
--   The analysis of RISRO at step $t$ uses: orthonormal $U\in\mathbb O_{p_1,r}$, $V\in\mathbb O_{p_2,r}$ with orthonormal complements, and a matrix of the form
--
--   $$
--   X=USV^\top,\qquad S\in\mathbb R^{r\times r}.
--   $$
--
--   Every iterate of every run of Algorithm 1 has this form. $S$ may be singular, and $\operatorname{rank}X=r$ is not part of the definition.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Algorithm 1, p.6, and Proposition 1, p.11

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_IsFrame

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The data of "the `t`-th iteration of RISRO" that the error analysis uses: `U ∈ 𝕆_{p₁,r}` and
`V ∈ 𝕆_{p₂,r}` with orthonormal complements, and `X = U S Vᵀ` for some `r × r` matrix `S`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Algorithm 1, p.6, and Proposition 1, p.11.

Formalization Note: every iterate of every run has this form (`IsRISRORun`): `X⁰` by the input
condition, and `X^{t+1} = X_U B† X_Vᵀ` because `X_U = U^{t+1} R`, `X_V = V^{t+1} R'`. `rank X = r`
is not assumed; `S` may be singular. -/
def IsIterate {p₁ p₂ r : ℕ} (U : Matrix (Fin p₁) (Fin r) ℝ)
    (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ) (V : Matrix (Fin p₂) (Fin r) ℝ)
    (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ) (X : Matrix (Fin p₁) (Fin p₂) ℝ) : Prop :=
  IsFrame U Uc ∧ IsFrame V Vc ∧ ∃ S : Matrix (Fin r) (Fin r) ℝ, X = U * S * Vᵀ

end RISRO


