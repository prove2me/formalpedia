-- Prove2me | Definitions.Def_TRSHolderKL_IsNonlinear
-- name    : TRSHolderKL_IsNonlinear
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:54.219429+00:00
-- url     : https://prove2.me/theorems/2e87d675-89a2-4121-a1be-d397d14a48f5
-- title:
--   Nonlinear inequality
-- statement:
--   An inequality $q(x)\le0$ is **nonlinear** if $q$ is not an affine function $x\mapsto c^Tx+d$. For a convex quadratic $q(x)=x^TQx+c^Tx+d$ this means $Q\neq0$.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Definitions 3.2–3.4, p.5

import Mathlib
import Definitions.Def_RBMSensitivity_E

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- An inequality `q(x) ≤ 0` is nonlinear when `q` is not affine,
Jiang and Li, arXiv:1911.11955v2, Definitions 3.2–3.4, p.5. -/
def IsNonlinear {n : ℕ} (q : E n → ℝ) : Prop :=
  ¬ ∃ c : E n, ∃ d : ℝ, ∀ x, q x = ⟪c, x⟫_ℝ + d

end TRSHolderKL


