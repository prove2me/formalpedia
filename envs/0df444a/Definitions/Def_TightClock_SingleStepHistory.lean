-- Prove2me | Definitions.Def_TightClock_SingleStepHistory
-- name    : TightClock_SingleStepHistory
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:48.015036+00:00
-- url     : https://prove2.me/theorems/baea461c-cb40-4be3-bb34-c6415a17376b
-- title:
--   History of a single-step clock
-- statement:
--   The history $H^t$ of a single-step clock after $t$ price tests: the sequence of tested bidders and acceptance or rejection outcomes. A test's offered price is a function of the earlier history, so it need not be recorded.
--
--   **Formalization Note** The page's $H^t$ also contains the realized tree and the seed. Those are fixed here, as parameters of the strategy.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.36 (PDF p.39)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- The history of a single-step clock, oldest test first: the sequence of tested bidders and their outcomes.
The offered prices are determined by these. Afshinmehr et al., manuscript (STOC 2027 submission), §6.2, p.36
(PDF 39). -/
abbrev SingleStepHistory (n : ℕ) : Type := List (Fin n × Bool)

end TightClock


