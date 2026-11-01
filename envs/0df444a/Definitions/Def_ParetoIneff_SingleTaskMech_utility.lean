-- Prove2me | Definitions.Def_ParetoIneff_SingleTaskMech_utility
-- name    : ParetoIneff_SingleTaskMech_utility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:33.673082+00:00
-- url     : https://prove2.me/theorems/4e7a1cc8-1942-4934-89e6-ff121dbe0601
-- title:
--   Utility in a single-task mechanism
-- statement:
--   For a single-task mechanism $\mathcal A=(x,p)$, reports $s\in\mathbb R_{\ge0}^n$ and a true cost vector $v$, the utility of machine $i$ is $p_i(s)-x_i(s)\,v_i$: its payment, minus its true cost if it receives the task.
--
--   This is the utility of §2 with $m=1$.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5, with one task

import Mathlib
import Definitions.Def_ParetoIneff_SingleTaskMech

open NNReal

namespace ParetoIneff

/-- The utility `p_i(s) − x_i(s) t_i` of machine `i` under the single-task mechanism `A` at the
reported vector `s` when its true processing time is `t_i = v i`, arXiv:1809.03454v7, p.5 with one
task. -/
def SingleTaskMech.utility {n : ℕ} (A : SingleTaskMech n) (v s : Fin n → ℝ≥0) (i : Fin n) : ℝ :=
  (A.pay s i : ℝ) - if A.alloc s = i then (v i : ℝ) else 0

end ParetoIneff


