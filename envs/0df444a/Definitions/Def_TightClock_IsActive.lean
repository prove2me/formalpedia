-- Prove2me | Definitions.Def_TightClock_IsActive
-- name    : TightClock_IsActive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:51:56.389646+00:00
-- url     : https://prove2.me/theorems/2fd41ebc-6360-4e5f-8eba-e22cbd8458be
-- title:
--   Active bidder at a history
-- statement:
--   A bidder is **active** at a history if every offer she has received so far was accepted. Every bidder is active at the start, and a bidder who rejects an offer is inactive forever after.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_History

set_option autoImplicit false

namespace TightClock

/-- A bidder is active at a history if she has rejected no offer: "An accepting bidder remains active,
whereas a rejecting bidder exits permanently." Afshinmehr et al., manuscript (STOC 2027 submission), §3,
p.13 (PDF 16). -/
def IsActive {n : ℕ} (h : History n) (i : Fin n) : Prop :=
  ∀ e ∈ h, e.bidder = i → e.accepted = true

end TightClock


