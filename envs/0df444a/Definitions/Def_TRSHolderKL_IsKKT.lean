-- Prove2me | Definitions.Def_TRSHolderKL_IsKKT
-- name    : TRSHolderKL_IsKKT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:53.820999+00:00
-- url     : https://prove2.me/theorems/d23e118e-ae0a-4d6b-bb94-2ee2ebc48400
-- title:
--   The KKT conditions of the TRS
-- statement:
--   A pair $(x^*,\lambda^*)\in\mathbb R^n\times\mathbb R$ satisfies the KKT conditions of (P$_0$) if
--   $$
--   \|x^*\|^2\le1,\quad (A+\lambda^*I)x^*=b,\quad A+\lambda^*I\succeq0,\quad \lambda^*\ge0,\quad \lambda^*(1-\|x^*\|^2)=0 .
--   $$
--   A point $x^*$ is optimal for (P$_0$) if and only if such a $\lambda^*$ exists; $\lambda^*$ is the Lagrange multiplier used to define the cases of Table 1.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The KKT conditions of (P₀) for a pair `(x*, λ*)`, Jiang and Li, arXiv:1911.11955v2, p.4:
`‖x*‖² ≤ 1`, `(A + λ*I)x* = b`, `A + λ*I ⪰ 0`, `λ* ≥ 0`, `λ*(1 − ‖x*‖²) = 0`. -/
def IsKKT {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) (x : E n) (lam : ℝ) : Prop :=
  ‖x‖ ^ 2 ≤ 1 ∧
  Matrix.toEuclideanLin (A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) x = b ∧
  (A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
  0 ≤ lam ∧ lam * (1 - ‖x‖ ^ 2) = 0

end TRSHolderKL


