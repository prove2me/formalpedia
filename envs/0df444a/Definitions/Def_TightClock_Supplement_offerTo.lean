-- Prove2me | Definitions.Def_TightClock_Supplement_offerTo
-- name    : TightClock_Supplement_offerTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:05:21.773388+00:00
-- url     : https://prove2.me/theorems/dd9887ec-9b35-4350-b19e-935ad58a64a4
-- title:
--   Offer a price and update the public state
-- statement:
--   Offer the price $p$ to bidder $i$. If she accepts ($v_i\ge p$) her current price becomes $p$; if she rejects she exits permanently. The operation returns her answer and the updated state.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_Supplement_ClockProg
import Definitions.Def_TightClock_Supplement_CState

set_option autoImplicit false

namespace TightClock.Supplement

/-- Offer the price `p` to bidder `i` and update the public state: on acceptance her current price
becomes `p`; on rejection she exits. Returns the answer and the new state. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, p.13 (PDF 16):
"An accepting bidder remains active, whereas a rejecting bidder exits permanently." -/
def offerTo {n : ℕ} (st : CState n) (i : Fin n) (p : ℝ) : ClockProg n (Bool × CState n) :=
  ClockProg.bind (ClockProg.offer i p) fun b =>
    ClockProg.pure
      (if b then (true, { st with price := Function.update st.price i p })
       else (false, { st with active := st.active.erase i }))

end TightClock.Supplement


