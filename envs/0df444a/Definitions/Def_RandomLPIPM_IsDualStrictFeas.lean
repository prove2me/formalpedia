-- Prove2me | Definitions.Def_RandomLPIPM_IsDualStrictFeas
-- name    : RandomLPIPM_IsDualStrictFeas
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:15.974065+00:00
-- url     : https://prove2.me/theorems/d4f24ec5-c909-476f-b3eb-e62e20389ff4
-- title:
--   Strict dual feasibility for $(\mathrm{LP})$
-- statement:
--   The dual program of (LP) is $\max b^\top y$ subject to $A^\top y+s=c$, $s\ge0$. A vector $y\in\mathbb R^d$ is **strictly dual feasible** when the slack
--   $$s=c-A^\top y$$
--   is positive in every coordinate.
--
--   Together with strict primal feasibility and full row rank of $A$, this is the standing assumption of the paper on the general pair (LP); it guarantees that the central path exists.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (LP), p.4

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **Strict dual feasibility for (LP).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (LP), p.4: the dual program is
`max bᵀy` s.t. `Aᵀy + s = c`, `s ≥ 0`; `y` is *strictly feasible* when the slack
`s = c − Aᵀy` is positive in every coordinate. -/
def IsDualStrictFeas {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (c : Fin n → ℝ)
    (y : Fin d → ℝ) : Prop :=
  ∀ i, 0 < (c - Aᵀ *ᵥ y) i

end RandomLPIPM


