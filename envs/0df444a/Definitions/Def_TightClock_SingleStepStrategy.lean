-- Prove2me | Definitions.Def_TightClock_SingleStepStrategy
-- name    : TightClock_SingleStepStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:00:41.208192+00:00
-- url     : https://prove2.me/theorems/eba45bd0-2f18-415f-b504-2500fa46809b
-- title:
--   Single-step clock strategy
-- statement:
--   A **single-step clock**, for a fixed tree and fixed seed, is a function from the history of price tests to the next move.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_SingleStepHistory
import Definitions.Def_TightClock_SingleStepAction

set_option autoImplicit false

namespace TightClock

/-- A single-step clock (its tree and seed are fixed): a map from the history of price tests to the next move.
Afshinmehr et al., manuscript (STOC 2027 submission), §6.2, p.35 (PDF 38). -/
abbrev SingleStepStrategy (n : ℕ) : Type := SingleStepHistory n → SingleStepAction n

end TightClock


