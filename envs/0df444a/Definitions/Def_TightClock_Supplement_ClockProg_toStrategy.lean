-- Prove2me | Definitions.Def_TightClock_Supplement_ClockProg_toStrategy
-- name    : TightClock_Supplement_ClockProg_toStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:04:14.191046+00:00
-- url     : https://prove2.me/theorems/de1014fc-c67d-4bc9-abf5-6a7e4a8782ce
-- title:
--   The clock auction run by a clock program
-- statement:
--   A clock program whose result is the set of bidders to serve defines a deterministic clock auction (a map from histories to moves): at each history it makes the program's pending offer, or stops and serves the set $S$ once the program has returned $S$.
--
--   **Formalization Note** On histories the program cannot produce, or if it computes forever without offers, the clock stops and serves $\emptyset$. The strict rules (`IsStrictClock`) make such a stop visible: it violates the rule that every active bidder is served.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_Supplement_ClockProg_react

set_option autoImplicit false

namespace TightClock.Supplement

/-- The deterministic clock auction run by a clock program that returns the set to serve: at a
history, the pending offer of the program, or `stop S` once it has returned `S`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, p.13
(PDF 16).

**Formalization Note** On histories the program cannot produce, or if it diverges without making
offers, the clock stops and serves `∅`. Under `IsStrictClock` such a stop is visible: it violates the
strict rule whenever an active bidder remains. -/
noncomputable def ClockProg.toStrategy {n : ℕ} (x : ClockProg n (Finset (Fin n))) : Strategy n :=
  fun h =>
    match x.react h with
    | some (.ask i p _) => .offer i p
    | some (.done S) => .stop S
    | _ => .stop ∅

end TightClock.Supplement


