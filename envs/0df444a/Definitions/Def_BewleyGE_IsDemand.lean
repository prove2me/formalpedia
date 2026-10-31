-- Prove2me | Definitions.Def_BewleyGE_IsDemand
-- name    : BewleyGE_IsDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:22.166041+00:00
-- url     : https://prove2.me/theorems/3ed767ec-cf32-4b49-9f74-157e924fd2ab
-- title:
--   Demand function $x^*(c,p)$
-- statement:
--   A map $c\mapsto x(c)$ is a **demand function** at prices $p$ if, for every expenditure $c\ge0$, the bundle $x(c)$ lies in $X(c,p)$ and maximizes $U$ there:
--   $$
--   x(c)\in\operatorname*{argmax}_{x\in X(c,p)}U(x).
--   $$
--   Given savings, the split of spending across goods is a static choice; under strict concavity the maximizer is unique.
--
--   **Formalization Note** Values at $c<0$ are unconstrained and never used.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2.1, p.7; Definition 1(i), p.9

import Mathlib
import Definitions.Def_BewleyGE_Economy
import Definitions.Def_BewleyGE_budget

namespace BewleyGE

/-- **Demand function** `x*(c, p) = argmax_{x ∈ X(c, p)} U(x)`.
Light, arXiv:1906.06810v2, §2.1, p.7, and Definition 1(i), p.9.

`x` is a demand function at prices `p` when, for every expenditure `c ≥ 0`, the bundle `x c`
lies on the budget plane `X(c, p)` and maximizes `U` there.

**Formalization Note.** The argmax is stated as attainment (`x c` is feasible and no feasible
bundle has higher utility), so no `sSup` enters. Values of `x` at `c < 0` are unconstrained; they
are never used (expenditure `a − b` is nonnegative for `b ∈ C(a, p)`). -/
def IsDemand {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (x : ℝ → Fin n → ℝ) : Prop :=
  ∀ c, 0 ≤ c → x c ∈ budget p c ∧ ∀ z ∈ budget p c, E.U z ≤ E.U (x c)

end BewleyGE


