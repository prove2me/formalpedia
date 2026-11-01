-- Prove2me | Definitions.Def_ParetoIneff_SingleTaskMech_IsEq
-- name    : ParetoIneff_SingleTaskMech_IsEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:29.76377+00:00
-- url     : https://prove2.me/theorems/67ba5fb0-f391-4b36-888c-b896691170ac
-- title:
--   Equilibrium of a single-task mechanism
-- statement:
--   A report vector $s$ is an equilibrium of the single-task mechanism $\mathcal A$ with respect to the true cost vector $v$ if no machine can raise its utility by changing its own report to any $b\ge0$.
--
--   This is the equilibrium of §2 with $m=1$. Task-independent mechanisms decompose into this notion, task by task.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5, with one task

import Mathlib
import Definitions.Def_ParetoIneff_SingleTaskMech_utility

open NNReal

namespace ParetoIneff

/-- `s` is a **(pure Nash) equilibrium** of the single-task mechanism `A` with respect to the true
vector `v`, arXiv:1809.03454v7, p.5 with one task: no machine `i` gains by deviating to any report
`b ∈ ℝ≥0`. -/
def SingleTaskMech.IsEq {n : ℕ} (A : SingleTaskMech n) (v s : Fin n → ℝ≥0) : Prop :=
  ∀ (i : Fin n) (b : ℝ≥0), A.utility v (Function.update s i b) i ≤ A.utility v s i

end ParetoIneff


