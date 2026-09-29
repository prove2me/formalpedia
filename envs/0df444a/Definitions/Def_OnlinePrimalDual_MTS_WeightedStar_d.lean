-- Prove2me | Definitions.Def_OnlinePrimalDual_MTS_WeightedStar_d
-- name    : OnlinePrimalDual_MTS_WeightedStar_d
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:41:53.323525+00:00
-- url     : https://prove2.me/theorems/f5a34380-c76f-490f-a914-dd2c4b4cf87e
-- title:
--   The collapsed per-state transition charge d(i) = 2d′(i)
-- statement:
--   `d(i) := 2·centerDist i`, the per-state transition charge Lemma 6.1 and Lemma 6.2 use
--   throughout in place of the full metric.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 143

import Mathlib
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar

namespace OnlinePrimalDual.MTS

/-- `d(i) := 2d′(i)` (p. 143, "From now on we only use `d(i) = 2d′(i)` to denote the cost of
moving from state `i` to any other state"), the per-state transition charge Lemma 6.1 and 6.2
use throughout. -/
def WeightedStar.d {V : Type*} (ws : WeightedStar V) (v : V) : ℝ :=
  2 * ws.centerDist v

end OnlinePrimalDual.MTS


