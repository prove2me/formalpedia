-- Prove2me | Definitions.Def_TightClock_initialState
-- name    : TightClock_initialState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:53:16.025001+00:00
-- url     : https://prove2.me/theorems/40512958-a87b-4139-b088-b7b4796b18a4
-- title:
--   Initial state $J^0$
-- statement:
--   Initially every bidder has cutoff $L$: $J^0_i=L$ for all $i$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.36 (PDF p.39)

import Mathlib
import Definitions.Def_TightClock_State

set_option autoImplicit false

namespace TightClock

/-- The initial state `J⁰`: "Initially, J⁰ᵢ = L for every bidder i." Afshinmehr et al., manuscript
(STOC 2027 submission), §6.2, p.36 (PDF 39). -/
def initialState (q L : ℕ) : State q L := fun _ => some (Fin.last L)

end TightClock


