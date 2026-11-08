-- Prove2me | Definitions.Def_TightClock_B
-- name    : TightClock_B
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:36.843645+00:00
-- url     : https://prove2.me/theorems/09cf9bef-e676-4d4c-b311-f2c98da17130
-- title:
--   Parameter $B=L^3$, (6.1)
-- statement:
--   The parameter $B:=L^3$ of (6.1): one "portion" of welfare.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38), eq. (6.1)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- The portion `B := L³` of (6.1), a natural number. Afshinmehr et al., manuscript (STOC 2027 submission),
§6.2, p.35 (PDF 38). -/
def B (L : ℕ) : ℕ := L ^ 3

end TightClock


