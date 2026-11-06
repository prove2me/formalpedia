-- Prove2me | Definitions.Def_RandomLPIPM_roundBasis
-- name    : RandomLPIPM_roundBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:50.964539+00:00
-- url     : https://prove2.me/theorems/66a5be07-338b-4a83-9954-c224b5ce9aa4
-- title:
--   Rounding of Theorem 8.11: solve the basis system on the $d$ largest coordinates
-- statement:
--   Given $\hat x$, let $\hat B$ be the indices of its $d$ largest coordinates and $\hat N=[n]\setminus\hat B$. The rounding returns the solution $(x,y,s)$ of
--   $$A_{\hat B}x_{\hat B}=A\mathbf 1,\quad x_{\hat N}=0,\quad A^\top y+s=\mathbf 1,\quad s_{\hat B}=0$$
--   when this system has a unique solution (i.e. $A_{\hat B}$ is invertible).
--
--   It is the final step of the method of Theorem 1.1.
--
--   **Formalization Note** When the solution is not unique the value is the junk triple $(0,0,0)$, which is never dual feasible for LP(A) (for $n\ge1$) and so never counts as optimal.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.11, pp.73–74; proof of Theorem 1.1, p.81

import Mathlib
import Definitions.Def_RandomLPIPM_topBasis
import Definitions.Def_RandomLPIPM_IsBasisSolution

open Matrix

namespace RandomLPIPM

/-- **The rounding of Theorem 8.11.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.11, pp.73–74: take `B̂` = the indices of
the `d` largest coordinates of `x̂` and solve `A_B̂ x_B̂ = A1`, `x_N̂ = 0`, `Aᵀy + s = 1`, `s_B̂ = 0`.

`roundBasis A x̂` is the solution `(x, y, s)` of that system when it is unique, and `(0, 0, 0)`
otherwise.

**Formalization Note.** The system has a unique solution exactly when the `d × d` matrix `A_B̂` is
invertible. The junk value `(0, 0, 0)` is never a dual feasible point of LP(A) (`Aᵀ0 + 0 ≠ 1` when
`n ≥ 1`), so it can never count as an optimal solution. -/
noncomputable def roundBasis {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (xh : Fin n → ℝ) :
    (Fin n → ℝ) × (Fin d → ℝ) × (Fin n → ℝ) := by
  classical
  exact if h : ∃! p : (Fin n → ℝ) × (Fin d → ℝ) × (Fin n → ℝ),
      IsBasisSolution A (topBasis d xh) p.1 p.2.1 p.2.2 then h.choose else (0, 0, 0)

end RandomLPIPM


