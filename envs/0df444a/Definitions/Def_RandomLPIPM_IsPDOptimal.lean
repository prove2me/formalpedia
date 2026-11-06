-- Prove2me | Definitions.Def_RandomLPIPM_IsPDOptimal
-- name    : RandomLPIPM_IsPDOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:16.156201+00:00
-- url     : https://prove2.me/theorems/b329ec2c-b593-4416-b234-bc40d92f9c52
-- title:
--   Optimal primal-dual solution of $(\mathrm{LP})$
-- statement:
--   A triple $(x,y,s)$ is an **optimal primal-dual solution** of (LP) with data $(A,b,c)$ when
--   1. $x\ge 0$ and $Ax=b$ (primal feasibility),
--   2. $A^\top y+s=c$ and $s\ge0$ (dual feasibility),
--   3. $c^\top x=b^\top y$ (zero duality gap).
--
--   By weak duality this is exactly optimality of $x$ for the primal and of $(y,s)$ for the dual. For LP(A) take $b=A\mathbf 1_n$, $c=\mathbf 1_n$.
--
--   This is what "the optimal primal and dual solutions" of Theorem 1.1 and "the optimal solution $(x^*,s^*)$" of Section 8 mean.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (LP), p.4; LP(A), p.5 and p.68

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **Primal-dual optimal solution of (LP).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (LP), p.4 (and LP(A), p.5 and p.68):
`(x, y, s)` is a pair of optimal solutions when `x` is primal feasible (`Ax = b`, `x ≥ 0`),
`(y, s)` is dual feasible (`Aᵀy + s = c`, `s ≥ 0`) and the objective values coincide,
`cᵀx = bᵀy`. By weak duality this is exactly primal and dual optimality. For LP(A) take
`b = A1`, `c = 1`. -/
def IsPDOptimal {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin d → ℝ) (s : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ A *ᵥ x = b ∧ Aᵀ *ᵥ y + s = c ∧ (∀ i, 0 ≤ s i) ∧ c ⬝ᵥ x = b ⬝ᵥ y

end RandomLPIPM


