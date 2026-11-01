-- Prove2me | Definitions.Def_RISRO_IsFrame
-- name    : RISRO_IsFrame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:44.853408+00:00
-- url     : https://prove2.me/theorems/3e6a64ef-a9bb-425d-8705-e75980dd15fe
-- title:
--   Orthonormal frame $U$ with orthonormal complement $U_\perp$
-- statement:
--   Let $U\in\mathbb R^{p\times r}$ and $U_\perp\in\mathbb R^{p\times(p-r)}$. The pair $(U,U_\perp)$ is an **orthonormal frame with complement** when
--
--   $$
--   U^\top U=I_r,\qquad U_\perp^\top U_\perp=I_{p-r},\qquad U^\top U_\perp=0,
--   $$
--
--   that is, $U\in\mathbb O_{p,r}$, $U_\perp\in\mathbb O_{p,p-r}$, and $[U\ U_\perp]$ is an orthogonal matrix.
--
--   This is the setting of the sketching step of RISRO: the complement is any orthonormal basis of the orthogonal complement of the column space of $U$, not a canonical one.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Section 1.4, p.5

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- `U` and `Uc` are an orthonormal frame and its orthonormal complement: `U ∈ 𝕆_{p,r}`,
`Uc ∈ 𝕆_{p,p-r}` and `Uᵀ Uc = 0`, so that `[U Uc]` is a `p × p` orthogonal matrix.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, §1.4, p.5 (`𝕆_{p,r}`, `U_⊥`).

Formalization Note: `U_⊥` is any orthonormal complement, as on the page; it is not a function of
`U`. `p - r` is natural-number subtraction, but `Uᵀ U = 1` already forces `r ≤ p`. -/
def IsFrame {p r : ℕ} (U : Matrix (Fin p) (Fin r) ℝ) (Uc : Matrix (Fin p) (Fin (p - r)) ℝ) : Prop :=
  Uᵀ * U = 1 ∧ Ucᵀ * Uc = 1 ∧ Uᵀ * Uc = 0

end RISRO


