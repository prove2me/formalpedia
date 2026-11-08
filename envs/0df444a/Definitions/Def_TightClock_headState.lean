-- Prove2me | Definitions.Def_TightClock_headState
-- name    : TightClock_headState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:54:08.023476+00:00
-- url     : https://prove2.me/theorems/d703c8d8-c8a1-49fc-a0d4-5df8d219313a
-- title:
--   State after an accepted price test
-- statement:
--   The state $J^+$ after a head for bidder $i$: her cutoff moves from $j$ to $j-1$, and all other bidders are unchanged.
--
--   **Formalization Note** The update is used at cutoffs $j\ge1$, where the natural subtraction is exact.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_State

set_option autoImplicit false

namespace TightClock

/-- The state after a head for the bidder `i`: she moves from cutoff `j` to cutoff `j − 1`. Afshinmehr et al.,
manuscript (STOC 2027 submission), §6.2, p.35 (PDF 38): "With a head she accepts and moves to cutoff j − 1".

**Formalization Note** It is used at cutoffs `j ≥ 1`, where the natural subtraction is exact. -/
def headState {q L : ℕ} (J : State q L) (i : Fin (bidderCount q L)) : State q L :=
  Function.update J i ((J i).map (fun j => ⟨j.val - 1, by have := j.isLt; omega⟩))

end TightClock


