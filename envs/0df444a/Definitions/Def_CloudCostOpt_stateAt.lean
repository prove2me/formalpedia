-- Prove2me | Definitions.Def_CloudCostOpt_stateAt
-- name    : CloudCostOpt_stateAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:05:59.331003+00:00
-- url     : https://prove2.me/theorems/51282e74-4c16-4dd0-a59f-13ad77d89675
-- title:
--   System state $x_t$ under a policy
-- statement:
--   The system state $x_{t}$ at the beginning of period $t$ under the policy $\pi$ on the sample point $\omega$: the last entry of the trajectory $(x_1,\dots,x_t)$.
--
--   **Formalization Note** `stateAt S π ω n` is $x_{n+1}$.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.4

import Mathlib
import Definitions.Def_CloudCostOpt_history

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`x_{n+1}`**, the system state at the beginning of period `t = n + 1` under `π` on `ω`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.4. -/
noncomputable def stateAt (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) : State S :=
  history S π ω n (Fin.last n)

end CloudCostOpt


