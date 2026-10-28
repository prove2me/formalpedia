-- Prove2me | Definitions.Def_fd05_discountedSurvivalPathPrice
-- name    : fd05_discountedSurvivalPathPrice
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:37:31.739377+00:00
-- url     : https://prove2.me/theorems/6291b6c6-bf03-4e7f-bd25-61c4d41f0b43
-- title:
--   Explicit discounted knock-out path-sum price
-- statement:
--   The knock-out price is the discounted sum over all N-step risk-neutral paths surviving every monitored upper-barrier observation.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd05_historySpot
import Definitions.Def_fd05_firstUpperHit
import Definitions.Def_fd05_historyWeight

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Independent finite-path expectation with zero value on hit histories. -/
noncomputable def discountedSurvivalPathPrice (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) : ℝ := by
  classical
  exact (m.growth ^ N)⁻¹ *
    Finset.univ.sum (fun ω : Fin N → Bool =>
      historyWeight m (List.ofFn ω) *
        (if N < firstUpperHit m N B monitor (List.ofFn ω)
         then g (historySpot m (List.ofFn ω)) else 0))

end FinancialDerivatives.FD05


