-- Prove2me | Definitions.Def_ParetoIneff_Mech_C
-- name    : ParetoIneff_Mech_C
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:15.646777+00:00
-- url     : https://prove2.me/theorems/1fd80005-b37a-4f21-9ef6-d9ab8543c1e0
-- title:
--   Makespan $C^{\mathcal M}(s\mid t)$
-- statement:
--   The makespan of the mechanism $\mathcal M$ at the reported profile $s$ under the true profile $t$ is the largest load over the machines,
--   $$
--   C^{\mathcal M}(s\mid t)=\max_{i\in N}\sum_{j=1}^m x_{i,j}(s)\,t_{i,j}.
--   $$
--   Reports decide the allocation; the true costs decide the load.
--
--   **Formalization Note** This is the published makespan of unrelated-machine scheduling applied to the allocation $x(s)$.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_ParetoIneff_Mech
import Definitions.Def_ParetoIneff_costMatrix

open NNReal

namespace ParetoIneff

/-- The makespan `C(s | t) = max_{i ∈ N} ∑_{j=1}^m x_{i,j}(s) t_{i,j}` of `ℳ` at the reported
profile `s` under the true profile `t`, arXiv:1809.03454v7, p.5: the published
`MatousekLP.Scheduling.makespan` of the allocation `x(s)` with the running times `t`. -/
noncomputable def Mech.C {n : ℕ} (M : Mech n) (m : ℕ) (s t : Fin n → Fin m → ℝ≥0) : ℝ :=
  MatousekLP.Scheduling.makespan (costMatrix t) (M.alloc m s)

end ParetoIneff


