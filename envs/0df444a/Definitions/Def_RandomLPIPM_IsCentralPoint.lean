-- Prove2me | Definitions.Def_RandomLPIPM_IsCentralPoint
-- name    : RandomLPIPM_IsCentralPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:11.995053+00:00
-- url     : https://prove2.me/theorems/3b0c1420-fc95-4ea9-a349-eb20469a82f1
-- title:
--   Central path point of $(\mathrm{LP})$: minimizer of $F_\mu$ over the strictly feasible points
-- statement:
--   A vector $x$ is a **central path point** of (LP) at parameter $\mu$ when $x$ is strictly feasible ($Ax=b$, $x>0$) and
--   $$F_\mu(x)\le F_\mu(x')\qquad\text{for every strictly feasible }x' ,$$
--   where $F_\mu(x)=c^\top x/\mu-\sum_i\log x_i$. Equivalently, $x$ minimizes $c^\top x-\mu\sum_i\log x_i$ over $\{Ax=b,\ x>0\}$, which is how the paper introduces the central path.
--
--   This predicate characterizes the point $x(\mu)$ that every result about the central path refers to.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), p.4 (central path); §9.1, p.77 ($x(\mu)=\arg\min F_\mu$)

import Mathlib
import Definitions.Def_RandomLPIPM_IsPrimalStrictFeas
import Definitions.Def_RandomLPIPM_barrier

open Matrix

namespace RandomLPIPM

/-- **Central path point of (LP), barrier form.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), p.77: "the central path point at `μ`
is `x(μ) := argmin_{x : Ax = b, x ≥ 0} F_μ(x)`"; p.4: "`x_μ` minimizes `cᵀx − μ ∑ log xᵢ` over
`{Ax = b, x > 0}`". `IsCentralPoint A b c μ x` says that `x` is strictly feasible and minimizes
`F_μ` over all strictly feasible points. -/
def IsCentralPoint {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ)
    (μ : ℝ) (x : Fin n → ℝ) : Prop :=
  IsPrimalStrictFeas A b x ∧
    ∀ x', IsPrimalStrictFeas A b x' → barrier c μ x ≤ barrier c μ x'

end RandomLPIPM


