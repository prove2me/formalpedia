-- Prove2me | Definitions.Def_TightClock_testPrice
-- name    : TightClock_testPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:01:22.581181+00:00
-- url     : https://prove2.me/theorems/27c3b9d0-3b50-4912-affb-0fcbc03d355d
-- title:
--   Price of a price test
-- statement:
--   A price test picks an active bidder with some cutoff $j\ge1$ and offers her the price $y_{j-1}$, which reveals her next coin.
--
--   **Formalization Note** Valid clocks test only active bidders with $j\ge1$, where the natural subtraction is exact. The value for an inactive bidder is never used.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_State
import Definitions.Def_TightClock_y

set_option autoImplicit false

namespace TightClock

/-- The price of a test: a bidder with cutoff `j ≥ 1` is offered `y_{j−1}`. Afshinmehr et al., manuscript (STOC
2027 submission), §6.2, p.35 (PDF 38).

**Formalization Note** Valid clocks test only active bidders with `j ≥ 1`, where the natural subtraction is
exact. The value `0` for an inactive bidder is never used. -/
noncomputable def testPrice (q L : ℕ) (J : State q L) (i : Fin (bidderCount q L)) : ℝ :=
  match J i with
  | some j => y q L (j.val - 1)
  | none => 0

end TightClock


