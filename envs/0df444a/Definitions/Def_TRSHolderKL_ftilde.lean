-- Prove2me | Definitions.Def_TRSHolderKL_ftilde
-- name    : TRSHolderKL_ftilde
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:42.567328+00:00
-- url     : https://prove2.me/theorems/3846f488-e798-4158-8d88-2a9669bb0eaa
-- title:
--   The relaxed objective $\tilde f$ of (P$_1$)
-- statement:
--   The objective of the convex relaxation (P$_1$):
--   $$
--   \tilde f(x)=x^T(A-\lambda_1I)x-2b^Tx+\lambda_1 ,
--   $$
--   where $\lambda_1$ is the smallest eigenvalue of $A$. On the unit ball $\tilde f(x)=f(x)-\lambda_1(x^Tx-1)$, so $\tilde f\le f$ there when $\lambda_1<0$, with equality on the unit sphere.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, (P1), p.3

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_lam1

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The objective `f̃(x) := xᵀ(A − λ₁I)x − 2bᵀx + λ₁` of the convex relaxation (P₁),
Jiang and Li, arXiv:1911.11955v2, p.3. -/
noncomputable def ftilde {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) (x : E n) : ℝ :=
  ⟪x, Matrix.toEuclideanLin (A - lam1 A • (1 : Matrix (Fin n) (Fin n) ℝ)) x⟫_ℝ
    - 2 * ⟪b, x⟫_ℝ + lam1 A

end TRSHolderKL


