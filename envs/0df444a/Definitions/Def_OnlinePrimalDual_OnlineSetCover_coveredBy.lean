-- Prove2me | Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
-- name    : OnlinePrimalDual_OnlineSetCover_coveredBy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:38:49.406293+00:00
-- url     : https://prove2.me/theorems/ca49b818-1d27-47d5-bee4-f28c0def604f
-- title:
--   Element e is covered by cover C (e ∈ C̄)
-- statement:
--   Element `e` is covered by the current cover `C` when some chosen set in `C` contains it
--   (the book's `C̄`, the union of the elements covered by members of `C`).
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 136, PDF p. 47

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance

namespace OnlinePrimalDual.OnlineSetCover

/-- Element `e` is covered by the current cover `C`, i.e. `e ∈ C̄` in the book's notation
(p. 136, PDF p. 47: "Define `C̄` to be the union of all the elements covered by members of
`C`"): some chosen set `t ∈ C` contains `e`. -/
def coveredBy {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (C : Finset T) (e : E) : Prop :=
  ∃ t ∈ inst.elemSets e, t ∈ C

end OnlinePrimalDual.OnlineSetCover


