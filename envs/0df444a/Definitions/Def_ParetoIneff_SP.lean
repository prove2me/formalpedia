-- Prove2me | Definitions.Def_ParetoIneff_SP
-- name    : ParetoIneff_SP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:59.375914+00:00
-- url     : https://prove2.me/theorems/b9c2826a-e57c-43f8-9bfd-1bb4d3b75937
-- title:
--   Second-price mechanism with $\alpha$-relative reserve price $\mathcal{SP}_\alpha$
-- statement:
--   The mechanism $\mathcal{SP}_\alpha$ on $n$ machines runs, independently for each task $j$, the single-task second-price mechanism with $\alpha$-relative reserve on the reports $s^j$, with ties broken by a given rule, and pays each machine the sum of its payments over the tasks.
--
--   As $\alpha$ runs from $1$ to $\infty$ these mechanisms interpolate between First-Price and Second-Price.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Definition 6, p.16

import Mathlib
import Definitions.Def_ParetoIneff_Mech
import Definitions.Def_ParetoIneff_col
import Definitions.Def_ParetoIneff_TieRule
import Definitions.Def_ParetoIneff_SPComp

open NNReal

namespace ParetoIneff

/-- The **second-price mechanism with `α`-relative reserve price** `𝒮𝒫_α`, Definition 6,
arXiv:1809.03454v7, p.16: the task-independent mechanism that runs, for each task `j`, the component
`𝒮𝒫_α^j` (`SPComp`) with the tie-breaking rule's choice for task `j` on the reports `sʲ` for that
task, and pays each machine the sum over tasks of its component payments. -/
noncomputable def SP {n : ℕ} (α : ℝ) (τ : TieRule n) : Mech n where
  alloc m s j := τ.pick m j (col s j)
  pay m s i := ∑ j : Fin m, (SPComp α (τ.pick m j)).pay (col s j) i

end ParetoIneff


