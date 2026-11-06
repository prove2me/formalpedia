-- Prove2me | Definitions.Def_RandomLPIPM_IsPrimalStrictFeas
-- name    : RandomLPIPM_IsPrimalStrictFeas
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:18.489246+00:00
-- url     : https://prove2.me/theorems/d124084a-b80d-460c-b4d7-bc66332c06e9
-- title:
--   Strict primal feasibility for $(\mathrm{LP})$
-- statement:
--   For $A\in\mathbb R^{d\times n}$ and $b\in\mathbb R^d$, the primal program of the pair (LP) is $\min c^\top x$ subject to $Ax=b$, $x\ge 0$. A point $x\in\mathbb R^n$ is **strictly feasible** when
--   $$Ax=b\qquad\text{and}\qquad x_i>0\ \text{ for every } i\in[n].$$
--   For the Gaussian program LP(A) the right-hand side is $b=A\mathbf 1_n$, and $x=\mathbf 1_n$ is strictly feasible.
--
--   Strict feasibility is the domain of the log-barrier, of the central path and of every iterate of the path-following method.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (LP), p.4; LP(A), p.5

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **Strict primal feasibility for (LP).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (LP), p.4: the primal program is
`min cᵀx` s.t. `Ax = b`, `x ≥ 0`; a point is *strictly feasible* when `Ax = b` and `x > 0`
coordinatewise. For LP(A) (p.5) the right-hand side is `b = A1`. -/
def IsPrimalStrictFeas {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ i, 0 < x i

end RandomLPIPM


