-- Prove2me | Definitions.Def_TightClock_OfferRecord
-- name    : TightClock_OfferRecord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:23.05232+00:00
-- url     : https://prove2.me/theorems/d7c5fb54-513c-48e7-bc1c-bb461d9827ed
-- title:
--   One offer in a clock auction's history
-- statement:
--   A clock auction observes only offers and answers. One record is a triple: a bidder, the price offered to her, and whether she accepted.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- One entry of the public history of a clock auction: the bidder, the price offered to her, and
whether she accepted. Afshinmehr et al., manuscript (STOC 2027 submission), §3, p.13 (PDF 16). -/
structure OfferRecord (n : ℕ) where
  /-- The bidder who received the offer. -/
  bidder : Fin n
  /-- The offered price. -/
  price : ℝ
  /-- Whether she accepted. -/
  accepted : Bool

end TightClock


