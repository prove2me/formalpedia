-- Prove2me | Definitions.Def_TightClock_History
-- name    : TightClock_History
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:42:56.032068+00:00
-- url     : https://prove2.me/theorems/b09d2a0f-7a76-4716-b735-dec0d4d1ae01
-- title:
--   Observed history of a clock auction
-- statement:
--   The **history** of a clock auction is the list of all offers made so far, each with the bidder's answer, oldest first. By §3, this is what an auction may react to, besides its public random seed.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_OfferRecord

set_option autoImplicit false

namespace TightClock

/-- The observed acceptance/rejection history of a clock auction, oldest offer first. Afshinmehr et al.,
manuscript (STOC 2027 submission), §3, p.13 (PDF 16). -/
abbrev History (n : ℕ) : Type := List (OfferRecord n)

end TightClock


