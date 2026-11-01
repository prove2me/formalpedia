-- Prove2me | Definitions.Def_LocalDOvS_SUS_ptVals
-- name    : LocalDOvS_SUS_ptVals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:11.033626+00:00
-- url     : https://prove2.me/theorems/5c84226e-5c8a-4d39-9bd7-dc995a3e05df
-- title:
--   Outputs of a decision in a history
-- statement:
--   For a history $h$ and a decision $x$, the list of outputs observed at $x$ in $h$, in the order they were observed. Its length is the number of simulations of $x$ made so far, and its $j$-th entry is $F(x,\xi_{x,j+1})$.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §1.2, p.7

import Mathlib

namespace LocalDOvS.SUS

/-- The outputs observed at decision `x` in a history `h`, in the order they were observed
(Zhang–Zheng–Lavaei, arXiv:2012.02427v2, §1.2, p.7: the evaluations `F(x, ξ_{x,j})`). Its length
is the number of simulations of `x` made so far. -/
def ptVals (h : List (ℕ × ℝ)) (x : ℕ) : List ℝ :=
  (h.filter (fun p => p.1 == x)).map Prod.snd

end LocalDOvS.SUS


