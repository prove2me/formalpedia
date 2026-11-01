-- Prove2me | Definitions.Def_ParetoIneff_OPT
-- name    : ParetoIneff_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:00.066567+00:00
-- url     : https://prove2.me/theorems/3fc8de78-dd7b-4ed2-b941-50e73a660b14
-- title:
--   Optimal makespan $\mathrm{OPT}(t)$
-- statement:
--   The optimal makespan of a profile $t$ is the minimum, over all feasible allocations $y$ of the $m$ tasks to the $n$ machines, of the makespan under true costs:
--   $$
--   \mathrm{OPT}(t)=\min_y\max_{i\in N}\sum_{j=1}^m y_{i,j}\,t_{i,j}.
--   $$
--   It is the denominator of both notions of inefficiency.
--
--   **Formalization Note** The minimum is an infimum over a finite type, which is nonempty for $n\ge1$.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_ParetoIneff_costMatrix

open NNReal

namespace ParetoIneff

/-- The optimal makespan `OPT(t) = min_y max_{i ∈ N} ∑_j y_{i,j} t_{i,j}` over all feasible
allocations `y` of the `m` tasks to the `n` machines, arXiv:1809.03454v7, p.5.

**Formalization Note** The minimum is the infimum over the finite type `Fin m → Fin n`. That type
is nonempty when `n ≥ 1` (or `m = 0`), and every theorem of the mission assumes `n ≥ 1`, so the
infimum is attained and never the junk value of an empty real infimum. -/
noncomputable def OPT {n m : ℕ} (t : Fin n → Fin m → ℝ≥0) : ℝ :=
  ⨅ y : Fin m → Fin n, MatousekLP.Scheduling.makespan (costMatrix t) y

end ParetoIneff


