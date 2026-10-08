-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_payoff2x2
-- name    : YoungConventions_RiskDominance_payoff2x2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:24.088252+00:00
-- url     : https://prove2.me/theorems/6b12fb8b-289d-4172-be67-0e917017fa2e
-- title:
--   Payoffs of the $2\times2$ game with table $(a_{rc},b_{rc})$
-- statement:
--   The $2\times2$ game written as
--   $$\begin{array}{c|cc} & 1 & 2\\\hline 1 & a_{11},b_{11} & a_{12},b_{12}\\ 2 & a_{21},b_{21} & a_{22},b_{22}\end{array}$$
--   gives Row the payoff $a_{rc}$ and Column the payoff $b_{rc}$ when Row plays $r$ and Column plays $c$.
--
--   **Formalization Note** The paper's $a_{11},a_{12},a_{21},a_{22}$ are `a 0 0, a 0 1, a 1 0, a 1 1`.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_Strat2

namespace YoungConventions.RiskDominance

/-- **Payoffs of the `2 × 2` game with table `(a_rc, b_rc)`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70 (PDF p. 15):
"Without loss of generality we may write `Γ` in the form" of the table whose cell in row `r` and
column `c` is `a_rc, b_rc`.

Row (player `0`) receives `a_rc` and Column (player `1`) receives `b_rc` when Row plays `r` and
Column plays `c`.

**Formalization Note.** Indices are shifted: the paper's `a₁₁, a₁₂, a₂₁, a₂₂` are
`a 0 0, a 0 1, a 1 0, a 1 1`. -/
def payoff2x2 (a b : Fin 2 → Fin 2 → ℝ) : Fin 2 → ((i : Fin 2) → Strat2 i) → ℝ :=
  fun i s => if i = 0 then a (s 0) (s 1) else b (s 0) (s 1)

end YoungConventions.RiskDominance


