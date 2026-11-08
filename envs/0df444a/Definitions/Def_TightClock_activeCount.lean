-- Prove2me | Definitions.Def_TightClock_activeCount
-- name    : TightClock_activeCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:00:20.160208+00:00
-- url     : https://prove2.me/theorems/8f1ec124-c579-49c4-b73b-4cfad2ce3a91
-- title:
--   Number of active bidders $\mathrm{act}(J)$
-- statement:
--   The number $\mathrm{act}(J)$ of bidders whose state at $J$ is not $\bot$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.6, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_TightClock_State

set_option autoImplicit false

namespace TightClock

/-- The number `act(J)` of active bidders at the state `J`. Afshinmehr et al., manuscript (STOC 2027
submission), §6.6, p.45 (PDF 48). -/
def activeCount {q L : ℕ} (J : State q L) : ℕ :=
  (Finset.univ.filter (fun i => J i ≠ none)).card

end TightClock


