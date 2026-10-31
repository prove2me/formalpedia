-- Prove2me | Definitions.Def_TRSHolderKL_IsConvexQuadratic
-- name    : TRSHolderKL_IsConvexQuadratic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:51.322954+00:00
-- url     : https://prove2.me/theorems/aff52cee-3627-4eff-8827-4bec906f91b5
-- title:
--   Convex quadratic function
-- statement:
--   A function $q:\mathbb R^n\to\mathbb R$ is a **convex quadratic** if
--   $$
--   q(x)=x^TQx+c^Tx+d
--   $$
--   for a symmetric positive semidefinite matrix $Q$, a vector $c$ and a scalar $d$. A system $q_i(x)\le0$, $i\in[m]$, of such inequalities is a convex quadratic system (Lemma 3.5).
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 3.5, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_E

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- A convex quadratic function `q(x) = xᵀQx + cᵀx + d` on `ℝⁿ` with `Q ⪰ 0`
(Jiang and Li, arXiv:1911.11955v2, Lemma 3.5, p.5, "convex quadratic system"). -/
def IsConvexQuadratic {n : ℕ} (q : E n → ℝ) : Prop :=
  ∃ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosSemidef ∧ ∃ c : E n, ∃ d : ℝ,
    ∀ x, q x = ⟪x, Matrix.toEuclideanLin Q x⟫_ℝ + ⟪c, x⟫_ℝ + d

end TRSHolderKL


