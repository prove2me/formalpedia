-- Prove2me | Definitions.Def_fd05_discountedFirstHitRebatePrice
-- name    : fd05_discountedFirstHitRebatePrice
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:39:33.317916+00:00
-- url     : https://prove2.me/theorems/932dc6c7-4439-46ab-b1ca-1d8351e0cd05
-- title:
--   Explicit first-touch discounted rebate sum
-- statement:
--   A rebate payable upon first touch is valued by its path probability and the discount factor to the actual payment time.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd05_firstUpperHit
import Definitions.Def_fd05_historyWeight

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Discount each rebate from its actual monitored first-hit time. -/
noncomputable def discountedFirstHitRebatePrice (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool) (Z : ℝ) : ℝ := by
  classical
  exact Finset.univ.sum (fun ω : Fin N → Bool =>
    historyWeight m (List.ofFn ω) *
      (if firstUpperHit m N B monitor (List.ofFn ω) ≤ N
       then Z / m.growth ^ (firstUpperHit m N B monitor (List.ofFn ω))
       else 0))

end FinancialDerivatives.FD05


