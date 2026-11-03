-- Prove2me | Definitions.Def_IsotropicSpin_yMat
-- name    : IsotropicSpin_yMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:28.104231+00:00
-- url     : https://prove2.me/theorems/e20d03fb-0a04-4fac-aa4c-0ba813b13b81
-- title:
--   The matrix $Y=\sum_k\xi_kS_k$ of eq. (18)
-- statement:
--   For a vector $\xi=(\xi_1,\xi_2,\xi_3)\in\mathbb C^3$, the $3\times3$ matrix of eq. (18) is
--
--   $$
--   Y=\sum_{k=1}^3\xi_kS_k ,
--   $$
--
--   with $S_k$ the spin-1 matrices (13). For a unit $\xi$, the matrix element $\langle\xi,\Omega\xi\rangle$ equals $\tfrac12\langle\phi,YY^\dagger\phi\rangle$, which is how $Y$ enters the bound (17).
--
--   **Formalization Note** Indices $0,1,2$ are the paper's $1,2,3$.
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (18), p.2

import Mathlib
import Definitions.Def_IsotropicSpin_spinOne

namespace IsotropicSpin

/-- **The matrix `Y`** of Alicki, arXiv:quant-ph/0402080v1, eq. (18), p. 2:
`Y = Σ_{k=1}^{3} ξ_k S_k` for a vector `ξ ∈ ℂ³`, with the spin-1 operators (13).

**Formalization Note** Indices `k = 0, 1, 2` are the paper's `1, 2, 3`. -/
noncomputable def yMat (ξ : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ∑ k, ξ k • spinOne k

end IsotropicSpin


