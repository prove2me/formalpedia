-- Prove2me | Definitions.Def_TRSHolderKL_grad
-- name    : TRSHolderKL_grad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:53.937237+00:00
-- url     : https://prove2.me/theorems/681caea1-805b-4aae-b4ae-15cd4b3123e0
-- title:
--   The gradient $\nabla f(x)=2(Ax-b)$
-- statement:
--   The vector
--   $$
--   \nabla f(x)=2(Ax-b).
--   $$
--   For a symmetric matrix $A$ this is the gradient of the TRS objective $f(x)=x^TAx-2b^Tx$; it appears in the KL inequality through the residual $\operatorname{dist}(-\nabla f(x),N_B(x))$.
--
--   **Formalization Note** The vector is defined by the explicit formula. That it is the gradient of $f$ for symmetric $A$ is checked in a verification file (not part of the mission).
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, display (27), p.15

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The gradient `∇f(x) = 2(Ax − b)` of the objective of (P₀) for symmetric `A`,
Jiang and Li, arXiv:1911.11955v2, display (27), p.15.

**Formalization Note.** Written as an explicit formula; it is the gradient of `f A b` when
`A` is symmetric (checked in `Solutions/verification/TRSHolderKL_Sanity.lean`). -/
noncomputable def grad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) (x : E n) : E n :=
  (2 : ℝ) • (Matrix.toEuclideanLin A x - b)

end TRSHolderKL


