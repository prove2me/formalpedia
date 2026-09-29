-- Prove2me | Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
-- name    : OnlinePrimalDual_OnlineSetCover_elementWeight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:38:13.125769+00:00
-- url     : https://prove2.me/theorems/acd0b299-19c2-4c8f-b11b-9c0f539398eb
-- title:
--   An element's weight, we = ∑_{s|e∈s} ws
-- statement:
--   Given a (monotonically increasing, over the run) assignment of fractional weights to sets
--   produced by Section 4.2's online fractional subroutine, an element's weight is the sum of the
--   weights of the sets containing it.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 136, PDF p. 47

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance

namespace OnlinePrimalDual.OnlineSetCover

/-- The weight of an element, `we := ∑_{s|e∈s} ws` (p. 136, PDF p. 47, "Let
`we = ∑_{s|e∈s} ws`"), given a (monotonically increasing, over the run) assignment `w` of
fractional weights to sets produced by Section 4.2's online fractional subroutine. -/
def elementWeight {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (e : E) : ℝ :=
  ∑ t ∈ inst.elemSets e, w t

end OnlinePrimalDual.OnlineSetCover


