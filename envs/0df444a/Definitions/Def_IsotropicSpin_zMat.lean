-- Prove2me | Definitions.Def_IsotropicSpin_zMat
-- name    : IsotropicSpin_zMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:17.085345+00:00
-- url     : https://prove2.me/theorems/14d5e459-d06a-4ad3-b1fe-042605d42a8a
-- title:
--   The matrix $Z=(\cos\alpha)S_3+i(\sin\alpha)((\cos\beta)S_3+(\sin\beta)S_1)$ of eq. (19)
-- statement:
--   For real numbers $\alpha,\beta$, the $3\times3$ matrix of eq. (19) is
--
--   $$
--   Z=(\cos\alpha)S_3+i(\sin\alpha)\big((\cos\beta)S_3+(\sin\beta)S_1\big),
--   $$
--
--   with $S_k$ the spin-1 matrices (13). Every $Y$ of (18) with unit $\xi$ is rotated into this form by the spin-1 representation, so $\|YY^\dagger\|=\|ZZ^\dagger\|$.
--
--   **Formalization Note** $S_3$ is `spinOne 2` and $S_1$ is `spinOne 0`.
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (19), p.2

import Mathlib
import Definitions.Def_IsotropicSpin_spinOne

namespace IsotropicSpin

/-- **The matrix `Z`** of Alicki, arXiv:quant-ph/0402080v1, eq. (19), p. 2:
`Z = (cos α) S₃ + i (sin α)((cos β) S₃ + (sin β) S₁)` for real `α, β`, with the spin-1 operators
(13).

**Formalization Note** `S₃ = spinOne 2` and `S₁ = spinOne 0` (Lean index = paper index − 1). -/
noncomputable def zMat (α β : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (Real.cos α : ℂ) • spinOne 2 +
    (Complex.I * Real.sin α) • ((Real.cos β : ℂ) • spinOne 2 + (Real.sin β : ℂ) • spinOne 0)

end IsotropicSpin


