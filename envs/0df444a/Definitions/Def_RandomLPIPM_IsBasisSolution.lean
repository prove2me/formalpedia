-- Prove2me | Definitions.Def_RandomLPIPM_IsBasisSolution
-- name    : RandomLPIPM_IsBasisSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:44.244621+00:00
-- url     : https://prove2.me/theorems/4471b2bf-11d2-4bf0-8b9b-d6baee28e521
-- title:
--   Solution of the basis system of Theorem 8.11
-- statement:
--   For a set $B\subseteq[n]$ with complement $N=[n]\setminus B$, a triple $(x,y,s)$ **solves the basis system** of LP(A) when
--   $$A_Bx_B=A\mathbf 1,\qquad x_N=0,\qquad A^\top y+s=\mathbf 1,\qquad s_B=0 .$$
--
--   **Formalization Note** $A_Bx_B=A\mathbf 1$ together with $x_N=0$ is written as $Ax=A\mathbf 1$ with $x_j=0$ for $j\notin B$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.11, pp.73–74

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **The basis system of Theorem 8.11.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.11, pp.73–74: for a basis `B` with
`N = [n] ∖ B`, `(x, y, s)` solves `A_B x_B = A1`, `x_N = 0`, `Aᵀy + s = 1`, `s_B = 0`.

**Formalization Note.** `A_B x_B = A1` together with `x_N = 0` is written as `Ax = A1` with
`x_j = 0` for `j ∉ B`. -/
def IsBasisSolution {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (B : Finset (Fin n))
    (x : Fin n → ℝ) (y : Fin d → ℝ) (s : Fin n → ℝ) : Prop :=
  (∀ j, j ∉ B → x j = 0) ∧ A *ᵥ x = A *ᵥ 1 ∧ Aᵀ *ᵥ y + s = 1 ∧ ∀ i ∈ B, s i = 0

end RandomLPIPM


