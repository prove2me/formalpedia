-- Prove2me | Definitions.Def_ParetoIneff_Mech_utility
-- name    : ParetoIneff_Mech_utility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:04.032954+00:00
-- url     : https://prove2.me/theorems/4a1bae80-1867-4659-aac3-010babfa98b2
-- title:
--   Utility of a machine
-- statement:
--   The utility of machine $i$ under a mechanism $\mathcal M=(x,p)$, with true processing times $t_i$ and reported profile $s$, is its payment minus the workload it has to execute:
--   $$
--   u_i^{\mathcal M}(s\mid t_i)=p_i(s)-\sum_{j=1}^m x_{i,j}(s)\,t_{i,j}.
--   $$
--   This is the quantity that a selfish machine maximizes by choosing its report.
--
--   **Formalization Note** The workload is the published load of machine $i$ under the allocation $x(s)$.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_ParetoIneff_Mech
import Definitions.Def_ParetoIneff_costMatrix

open NNReal

namespace ParetoIneff

/-- The utility `u_i(s | t_i) = p_i(s) − ∑_{j=1}^m x_{i,j}(s) t_{i,j}` of machine `i` under the
mechanism `ℳ` at the reported profile `s` when its true processing times are those of `t`,
arXiv:1809.03454v7, p.5.

**Formalization Note** The total workload `∑_j x_{i,j}(s) t_{i,j}` is the load of machine `i` under
the allocation `x(s)`, `MatousekLP.Scheduling.load`, with the map `x(s) : Fin m → Fin n`. -/
noncomputable def Mech.utility {n : ℕ} (M : Mech n) (m : ℕ) (t s : Fin n → Fin m → ℝ≥0)
    (i : Fin n) : ℝ :=
  (M.pay m s i : ℝ) - MatousekLP.Scheduling.load (costMatrix t) (M.alloc m s) i

end ParetoIneff


