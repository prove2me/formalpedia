-- Prove2me | Definitions.Def_BewleyGE_wealthSet
-- name    : BewleyGE_wealthSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:10.054602+00:00
-- url     : https://prove2.me/theorems/07b8f575-6a90-4a7c-88b3-528705f100aa
-- title:
--   Wealth levels $A(p,r)=[\underline a(p,r),\bar a(p,r)]$
-- statement:
--   For $p\gg0$ and $r\in(0,1)$, the **set of possible wealth levels** is $A(p,r)=[\underline a(p,r),\bar a(p,r)]$ with
--   $$
--   \underline a(p,r)=(1+r)\,\underline b(p,r)+\min_{y\in\mathcal Y}p\cdot y=-\frac{\min_{y}p\cdot y}{r},\qquad
--   \bar a(p,r)=(1+r)\sum_{i=1}^n\frac{p_i\bar b}{(1-r)^2}+\max_{y\in\mathcal Y}p\cdot y .
--   $$
--   It is the compact state space of the agents' problem: next-period wealth $(1+r)b+p\cdot y$ stays in $A(p,r)$ for every feasible $b$ and $y\in\mathcal Y$.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2.1, p.7

import Mathlib
import Definitions.Def_BewleyGE_borrowLimit
import Definitions.Def_BewleyGE_maxIncome
import Definitions.Def_BewleyGE_savingsCap

namespace BewleyGE

/-- **Wealth levels** `A(p, r) = [a̲(p, r), ā(p, r)]` with
`a̲(p, r) = (1 + r) b̲ + min_{y ∈ 𝒴} p · y` and
`ā(p, r) = (1 + r) ∑ᵢ pᵢ b̄/(1 − r)² + max_{y ∈ 𝒴} p · y`.
Light, arXiv:1906.06810v2, §2.1, p.7.

**Formalization Note.** `a̲` is written in the page's first form; for `r ≠ 0` it equals
`−min_{y} p · y / r`, the page's final form. Used only for `p ≫ 0`, `0 < r < 1`. -/
noncomputable def wealthSet {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ) : Set ℝ :=
  Set.Icc ((1 + r) * borrowLimit E p r + minIncome E p)
    ((1 + r) * savingsCap E p r + maxIncome E p)

end BewleyGE


