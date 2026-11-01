-- Prove2me | Definitions.Def_ParetoIneff_col
-- name    : ParetoIneff_col
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:54.282413+00:00
-- url     : https://prove2.me/theorems/5c1c1042-a7be-4738-a378-0501fea39956
-- title:
--   Column $t^j$ of a profile
-- statement:
--   For a profile $t\in\mathbb R_{\ge0}^{n\times m}$ and a task $j$, the column $t^j=(t_{1,j},\dots,t_{n,j})$ is the vector of processing times of the machines for task $j$. The same notation is used for reported profiles.
--
--   Columns are the inputs of the single-task components of a task-independent mechanism.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib

open NNReal

namespace ParetoIneff

/-- The column `tʲ = (t_{1,j}, …, t_{n,j})` of an `n × m` profile, arXiv:1809.03454v7, p.5: the
vector of processing times (or reports) of the machines for task `j`. -/
def col {n m : ℕ} (t : Fin n → Fin m → ℝ≥0) (j : Fin m) : Fin n → ℝ≥0 := fun i => t i j

end ParetoIneff


