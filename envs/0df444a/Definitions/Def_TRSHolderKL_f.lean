-- Prove2me | Definitions.Def_TRSHolderKL_f
-- name    : TRSHolderKL_f
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:53.863261+00:00
-- url     : https://prove2.me/theorems/a6af544d-9ac2-487d-ae5f-c1d8a27864bb
-- title:
--   The TRS objective $f(x)=x^TAx-2b^Tx$
-- statement:
--   For an $n\times n$ real matrix $A$ and $b\in\mathbb R^n$, the objective of the trust region subproblem (P$_0$) is
--   $$
--   f(x)=x^TAx-2b^Tx,\qquad x\in\mathbb R^n .
--   $$
--   Every statement of the mission concerns this quadratic function minimized over the unit ball.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, p.1, (P0)

import Mathlib
import Definitions.Def_RBMSensitivity_E

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- The objective `f(x) := xᵀAx − 2bᵀx` of the trust region subproblem (P₀),
Jiang and Li, arXiv:1911.11955v2, p.1. -/
noncomputable def f {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) (x : E n) : ℝ :=
  ⟪x, Matrix.toEuclideanLin A x⟫_ℝ - 2 * ⟪b, x⟫_ℝ

end TRSHolderKL


