-- Prove2me | Definitions.Def_RandomLPIPM_barrier
-- name    : RandomLPIPM_barrier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:21.165138+00:00
-- url     : https://prove2.me/theorems/cee99df8-5c3a-4680-bfc4-a5c5ee829b52
-- title:
--   Normalized log-barrier $F_\mu(x)=c^\top x/\mu-\sum_i\log x_i$
-- statement:
--   For $c\in\mathbb R^n$ and $\mu>0$, the normalized log-barrier of (LP) is
--   $$F_\mu(x)=\frac{c^\top x}{\mu}-\sum_{i=1}^n\log x_i ,\qquad x>0 .$$
--   The central path point $x(\mu)$ is its minimizer over the strictly feasible points.
--
--   **Formalization Note** Lean's logarithm is total ($\log t=0$ for $t\le 0$); the barrier is only compared over strictly feasible points, where every $x_i>0$.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), §9.1, p.77 (normalized log-barrier); p.8 for LP(A)

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **Normalized log-barrier `F_μ`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), §9.1, p.77: "The normalized log-barrier function
for LP is `F_μ(x) := cᵀx/μ − ∑ᵢ log(xᵢ)`". (Also p.8 for LP(A), where `c = 1`.)

**Formalization Note.** `Real.log` is total (`log t = 0` for `t ≤ 0`); the barrier is only ever
compared over strictly feasible points (`IsCentralPoint`), where every `xᵢ > 0`. -/
noncomputable def barrier {n : ℕ} (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ) : ℝ :=
  (c ⬝ᵥ x) / μ - ∑ i, Real.log (x i)

end RandomLPIPM


