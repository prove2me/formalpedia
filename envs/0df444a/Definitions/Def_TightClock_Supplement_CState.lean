-- Prove2me | Definitions.Def_TightClock_Supplement_CState
-- name    : TightClock_Supplement_CState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:04:27.591812+00:00
-- url     : https://prove2.me/theorems/5458555c-07d9-4fda-94d0-5d33e13028ac
-- title:
--   Public state of a clock auction: prices and active set
-- statement:
--   The public state tracked by the auctions: each bidder's **current price** $p_i$ (her last accepted offer, initially $0$) and the **active set** (the bidders who have not rejected an offer). A clock auction starts with every bidder active at price $0$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- The public state of a clock auction that the auctions below track: each bidder's current price
(her last accepted price, initially `0`) and the set of active bidders. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, p.13 (PDF 16): "A
clock auction starts with every bidder active at price 0." -/
structure CState (n : ℕ) where
  /-- Current price of each bidder: her last accepted offer, or `0`. -/
  price : Fin n → ℝ
  /-- The bidders who have rejected no offer. -/
  active : Finset (Fin n)

end TightClock.Supplement


