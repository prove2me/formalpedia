-- Prove2me | Definitions.Def_TightClock_Supplement_reveal
-- name    : TightClock_Supplement_reveal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:05:58.438204+00:00
-- url     : https://prove2.me/theorems/eb5c5391-aa05-4ca2-8417-97a80cbc8ee6
-- title:
--   $\mathrm{Reveal}(i)$
-- statement:
--   $\mathrm{Reveal}(i)$ makes successive grid offers $\delta(\lfloor q/\delta\rfloor+1)$ to bidder $i$, from her current price $q$, until she rejects. It returns her last accepted price and the updated state, in which she has exited. Started from price $0$ on a grid profile, the last accepted price is exactly $v_i$, so the operation learns her value and permanently removes her.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_Supplement_offerTo
import Definitions.Def_TightClock_Supplement_nextGrid

set_option autoImplicit false

namespace TightClock.Supplement

/-- `Reveal(i)`: successive grid offers `δ(⌊q/δ⌋+1)` to bidder `i` from her current price `q` until
she rejects; returns her last accepted price (her value, on the grid, when she starts at price
`0`) and the new state, in which she has exited. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, p.13 (PDF 16): "Reveal(i) makes
successive grid offers to bidder i until rejection, thereby learning vi and permanently removing
the bidder." -/
noncomputable def reveal {n : ℕ} (δ : ℝ) (st0 : CState n) (i : Fin n) : ClockProg n (ℝ × CState n) :=
  ClockProg.loop (fun st : CState n => do
    let (b, st') ← offerTo st i (nextGrid δ (st.price i))
    if b then return Sum.inl st' else return Sum.inr (st'.price i, st')) st0

end TightClock.Supplement


