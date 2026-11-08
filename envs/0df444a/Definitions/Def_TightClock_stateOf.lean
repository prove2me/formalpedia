-- Prove2me | Definitions.Def_TightClock_stateOf
-- name    : TightClock_stateOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:02:35.755673+00:00
-- url     : https://prove2.me/theorems/2735c49b-c0b8-4969-8cda-5d2218909b0b
-- title:
--   State determined by a history
-- statement:
--   A history of price tests determines the state: start with $J^0$; a head moves the tested bidder from cutoff $j$ to $j-1$, and a tail makes her inactive.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.36 (PDF p.39)

import Mathlib
import Definitions.Def_TightClock_SingleStepHistory
import Definitions.Def_TightClock_initialState
import Definitions.Def_TightClock_headState
import Definitions.Def_TightClock_tailState

set_option autoImplicit false

namespace TightClock

/-- The state `Jᵗ` determined by a history of price tests: start from `J⁰`, then a head lowers the tested
bidder's cutoff by one and a tail makes her inactive. Afshinmehr et al., manuscript (STOC 2027 submission),
§6.2, p.36 (PDF 39): "In particular, Jᵗ is determined by Hᵗ." -/
def stateOf (q L : ℕ) (h : SingleStepHistory (bidderCount q L)) : State q L :=
  h.foldl (fun J e => if e.2 then headState J e.1 else tailState J e.1) (initialState q L)

end TightClock


