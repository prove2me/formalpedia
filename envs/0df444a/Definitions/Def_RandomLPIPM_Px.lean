-- Prove2me | Definitions.Def_RandomLPIPM_Px
-- name    : RandomLPIPM_Px
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:44.469761+00:00
-- url     : https://prove2.me/theorems/ae52fe44-1934-4ac5-80cf-7b722628ede7
-- title:
--   Projector $P_x=I-XA^\top(AX^2A^\top)^{-1}AX$ onto $\ker(AX)$
-- statement:
--   For $A$ of full row rank and $x>0$ (so $X=\operatorname{Diag}(x)$ is a positive diagonal matrix),
--   $$P_x=I-XA^\top(AX^2A^\top)^{-1}AX$$
--   is the symmetric orthogonal projector onto $\ker(AX)$.
--
--   Applying $P_x$ to a vector costs one linear system solve in $ADA^\top$ with $D=X^2$ positive diagonal; this is the unit of cost in Theorem 1.1.
--
--   **Formalization Note** The printed formula. Lean's matrix inverse is total (it returns $0$ for a singular matrix); every statement using $P_x$ assumes full row rank and $x>0$, where $AX^2A^\top$ is invertible.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), §9.1, p.77; Algorithm 1, line 5, p.80

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **The projector `P_x` onto `ker(AX)`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), §9.1, p.77: "we use `P_x` to denote the
symmetric orthogonal projector onto `ker(AX)` where `x` is a strictly feasible solution to (LP) so
that `X` is a positive diagonal matrix, that is, `P_x = I − XAᵀ(AX²Aᵀ)⁻¹AX`" (line 5 of
Algorithm 1, p.80).

**Formalization Note.** The printed formula, with `X = Diag(x)`. Applying `P_x` to a vector is one
linear system solve in `AX²Aᵀ = ADAᵀ` with `D = X²` positive diagonal. Mathlib's matrix inverse is
total (`0` for a singular matrix); `AX²Aᵀ` is invertible when `A` has full row rank and `x > 0`, the
setting of every statement that uses `Px`. -/
noncomputable def Px {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 - diagonal x * Aᵀ * (A * diagonal x ^ 2 * Aᵀ)⁻¹ * A * diagonal x

end RandomLPIPM


