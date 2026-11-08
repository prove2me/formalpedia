-- Prove2me | Definitions.Def_TightClock_Strategy
-- name    : TightClock_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:49:08.874555+00:00
-- url     : https://prove2.me/theorems/6672f340-fd75-4472-a2a8-692670a93965
-- title:
--   Deterministic clock strategy
-- statement:
--   A **deterministic clock** is a function from histories to moves. "Prices may be raised adaptively as a function of the public random seed and the observed acceptance/rejection history": once the seed is fixed, the next move is a function of the history alone. In particular it does not see the values.
--
--   **Formalization Note** The strategy may depend on $\mathcal F$ and $D$, since it is chosen after them. Rounds are unbounded.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_History
import Definitions.Def_TightClock_ClockAction

set_option autoImplicit false

namespace TightClock

/-- A deterministic clock auction: a map from the observed history to the next move. It reads the
history and nothing else, so it never reads the values. Afshinmehr et al., manuscript (STOC 2027
submission), §3, p.13 (PDF 16).

**Formalization Note** The map may depend on `F` and `D`, since a strategy is chosen after them
(p.34: "they know F and D"). There is no bound on the number of rounds. -/
abbrev Strategy (n : ℕ) : Type := History n → ClockAction n

end TightClock


