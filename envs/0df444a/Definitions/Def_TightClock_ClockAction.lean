-- Prove2me | Definitions.Def_TightClock_ClockAction
-- name    : TightClock_ClockAction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:29.157678+00:00
-- url     : https://prove2.me/theorems/9e25661e-040c-46b5-8713-4cfeac4b5e48
-- title:
--   One move of a clock auction
-- statement:
--   At each point a clock auction either **offers** a real price $p$ to a bidder $i$, or **stops** and serves a set $S$ of bidders. Which moves are legal is the content of `IsValidClock`.
--
--   **Formalization Note** Prices are arbitrary reals here, not grid points: the auction class of Theorem 6.1 is not restricted to the prior's support.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16); §6.1, p.34 (PDF p.37)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- A move of a clock auction: offer a price to a bidder, or stop and serve a set. Afshinmehr et al.,
manuscript (STOC 2027 submission), §3, p.13 (PDF 16); §6.1, p.34 (PDF 37). -/
inductive ClockAction (n : ℕ) : Type
  /-- Offer the price `p` to the bidder `i`. -/
  | offer (i : Fin n) (p : ℝ) : ClockAction n
  /-- Terminate and serve the set `S`. -/
  | stop (S : Finset (Fin n)) : ClockAction n

end TightClock


