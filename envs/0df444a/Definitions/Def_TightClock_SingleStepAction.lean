-- Prove2me | Definitions.Def_TightClock_SingleStepAction
-- name    : TightClock_SingleStepAction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:39.489438+00:00
-- url     : https://prove2.me/theorems/f17f8462-bde7-4340-b3b4-fe3610ef0bbd
-- title:
--   One move of a single-step clock
-- statement:
--   At each step a **single-step clock** picks a bidder and runs a price test on her, or it stops and serves a set of bidders.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- A move of a single-step clock: run a price test on a bidder, or stop and serve a set. Afshinmehr et al.,
manuscript (STOC 2027 submission), §6.2, p.35 (PDF 38). -/
inductive SingleStepAction (n : ℕ) : Type
  /-- A price test of the bidder `i`, at the next value above her cutoff. -/
  | test (i : Fin n) : SingleStepAction n
  /-- Terminate and serve the set `S`. -/
  | stop (S : Finset (Fin n)) : SingleStepAction n

end TightClock


