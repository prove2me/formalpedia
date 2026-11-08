-- Prove2me | Definitions.Def_TightClock_tailState
-- name    : TightClock_tailState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:56:01.65955+00:00
-- url     : https://prove2.me/theorems/301bc450-0274-4f6e-a184-b045a8ade0ff
-- title:
--   State after a rejected price test
-- statement:
--   The state $J^-$ after a tail for bidder $i$: she becomes inactive, with state $\bot$, and all other bidders are unchanged.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_State

set_option autoImplicit false

namespace TightClock

/-- The state after a tail for the bidder `i`: she "declines and becomes inactive". Afshinmehr et al.,
manuscript (STOC 2027 submission), §6.2, p.35 (PDF 38). -/
def tailState {q L : ℕ} (J : State q L) (i : Fin (bidderCount q L)) : State q L :=
  Function.update J i none

end TightClock


