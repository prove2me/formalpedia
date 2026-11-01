-- Prove2me | Definitions.Def_RISRO_gradF
-- name    : RISRO_gradF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:30:48.627951+00:00
-- url     : https://prove2.me/theorems/cc5ce5e9-4540-4765-ba4d-c600d0adfd42
-- title:
--   Gradient $\nabla f(X)=\mathcal A^*(\mathcal A(X)-y)$
-- statement:
--   For the objective $f(X)=\tfrac12\|y-\mathcal A(X)\|_2^2$ of problem (1), the gradient is
--
--   $$
--   \nabla f(X)=\mathcal A^*(\mathcal A(X)-y).
--   $$
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, display (1), p.1, and p.11

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace RISRO

/-- The gradient `∇f(X) = A^*(A(X) - y)` of `f(X) = ½‖y - A(X)‖₂²`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, display (1), p.1, and p.11. -/
def gradF {p₁ p₂ n : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (X : Matrix (Fin p₁) (Fin p₂) ℝ) : Matrix (Fin p₁) (Fin p₂) ℝ :=
  observationOpAdjoint A (observationOp A X - y)

end RISRO


