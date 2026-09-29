-- Prove2me | Definitions.Def_OnlinePrimalDual_MTS_costNewPhases
-- name    : OnlinePrimalDual_MTS_costNewPhases
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:43:07.734903+00:00
-- url     : https://prove2.me/theorems/927232c4-2f48-40bc-9744-ff859cf6db8c
-- title:
--   Cost of a solution in the new MTS model
-- statement:
--   Given a solution's `k` phases (`s i` the state visited during phase `i`),
--   `costNewPhases := ∑ᵢ d(sᵢ)`: each phase costs exactly its state's charge, regardless of how
--   much service actually occurred.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 144-145

import Mathlib
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar_d

namespace OnlinePrimalDual.MTS

/-- The cost, in the **new** MTS model, of a solution described by the `k` phases it visits:
`s i` is the state visited during phase `i`, and each phase costs exactly `d(s i)` regardless of
how much service was actually performed during it (p. 144-145, "If the algorithm is in state `i`
during phase `p` then it pays a cost `d(i)`. The algorithm pays the full cost of the phase even
if it was in state `i` only during part of the phase"). -/
def costNewPhases {V : Type*} {k : ℕ} (ws : WeightedStar V) (s : Fin k → V) : ℝ :=
  ∑ i, ws.d (s i)

end OnlinePrimalDual.MTS


