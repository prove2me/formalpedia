-- Prove2me | Definitions.Def_OnlinePrimalDual_Caching_dualSum
-- name    : OnlinePrimalDual_Caching_dualSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:45:19.735905+00:00
-- url     : https://prove2.me/theorems/a846a4db-1295-42d1-9837-fbdaa569e14d
-- title:
--   Accumulated dual value charged against a caching variable's dual constraint
-- statement:
--   `dualSum inst y v := ∑_{t ∣ v ∈ S t} y t`, the left-hand side of inequality (7.1)'s bracketed
--   sum `∑_{t(p,j)+1 ≤ t ≤ t(p,j+1)-1} y(t)` before subtracting `z(p,j)`. Used to state the dual
--   near-feasibility bound (Eq. (7.2)) and as (part of) the argument to the algorithm's update rule
--   for `x(p,j)`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 152, inequality (7.1)

import Mathlib
import Definitions.Def_OnlinePrimalDual_Caching_CachingInstance

namespace OnlinePrimalDual.Caching

/-- The accumulated dual value `∑_{t | v ∈ S t} y t` charged against primal variable `v`'s dual
constraint, i.e. the left-hand-side sum `∑_{t(p,j)+1 ≤ t ≤ t(p,j+1)-1} y(t)` of inequality (7.1),
p. 152, PDF p. 63, before subtracting `z(p,j)`. Used both to state the dual near-feasibility bound
(Eq. (7.2), p. 155) and, in the algorithm's own update rule, as (part of) the argument driving
`cachingX`'s exponential increase. -/
def dualSum {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (v : V) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => v ∈ inst.S t), y t

end OnlinePrimalDual.Caching


