-- Prove2me | Definitions.Def_TightClock_C
-- name    : TightClock_C
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:45:42.265386+00:00
-- url     : https://prove2.me/theorems/345d4681-a09a-462c-aefa-d6d0b77dc705
-- title:
--   Ticket function $C(p)$, (6.7)
-- statement:
--   For $p\in[0,1]$,
--
--   $$C(p):=1+(e^a-1)p,$$
--
--   the expected payoff of a ticket that pays $e^a$ with probability $p$ and $1$ otherwise.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.4, p.39 (PDF p.42), eq. (6.7)

import Mathlib
import Definitions.Def_TightClock_a

set_option autoImplicit false

namespace TightClock

/-- The ticket function `C(p) := 1 + (eᵃ − 1) p` of (6.7). Afshinmehr et al., manuscript (STOC 2027
submission), §6.4, p.39 (PDF 42). -/
noncomputable def C (q : ℕ) (p : ℝ) : ℝ := 1 + (Real.exp (a q) - 1) * p

end TightClock


