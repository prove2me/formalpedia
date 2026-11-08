-- Prove2me | Definitions.Def_TightClock_M
-- name    : TightClock_M
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:37.68931+00:00
-- url     : https://prove2.me/theorems/317646db-da1a-41fe-a47c-671138fdf7fc
-- title:
--   Parameter $M=Lq^4$, (6.1)
-- statement:
--   The parameter $M:=Lq^4$ of (6.1): consecutive tier values differ by a factor $M$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38), eq. (6.1)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- The scale `M := L q⁴` of (6.1), a natural number. Afshinmehr et al., manuscript (STOC 2027 submission),
§6.2, p.35 (PDF 38). -/
def M (q L : ℕ) : ℕ := L * q ^ 4

end TightClock


