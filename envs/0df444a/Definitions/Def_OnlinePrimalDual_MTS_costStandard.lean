-- Prove2me | Definitions.Def_OnlinePrimalDual_MTS_costStandard
-- name    : OnlinePrimalDual_MTS_costStandard
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:42:35.869762+00:00
-- url     : https://prove2.me/theorems/76f2594a-f3a2-4b3a-befd-1bc31b5a20ac
-- title:
--   Cost of a solution in the standard MTS model
-- statement:
--   Given a solution's `k` runs (`s i` the state of run `i`, `w i` its service cost),
--   `costStandard := ∑ᵢ(wᵢ + d(sᵢ))`: each run's service cost plus one transition-out charge.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 144

import Mathlib
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar_d

namespace OnlinePrimalDual.MTS

/-- The cost, in the **standard** MTS model, of a solution described by its `k` runs: `s i` is
the state occupied during run `i`, `w i` is the service cost accumulated while in that state
(p. 144, "`si`... the algorithm pays for the cost for serving the requests in state `si`"), and
each run ends with a transition out of `si` costing `d(si)` (p. 144, "and then pays for moving
out of `si` at `ti`"). Matches the book's own per-run decomposition of the standard model's cost,
`∑ᵢ (Wᵢ + d(sᵢ))`, exactly. -/
def costStandard {V : Type*} {k : ℕ} (ws : WeightedStar V) (s : Fin k → V) (w : Fin k → ℝ) : ℝ :=
  ∑ i, (w i + ws.d (s i))

end OnlinePrimalDual.MTS


