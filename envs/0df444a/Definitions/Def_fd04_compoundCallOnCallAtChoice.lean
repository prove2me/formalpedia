-- Prove2me | Definitions.Def_fd04_compoundCallOnCallAtChoice
-- name    : fd04_compoundCallOnCallAtChoice
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:47:11.390197+00:00
-- url     : https://prove2.me/theorems/32aa09dc-8907-4f93-bf85-6e936dd48ecc
-- title:
--   Call-on-call exercise payoff
-- statement:
--   At the compound option's exercise date, its holder receives the positive part of the later-expiring underlying call value less compound strike L.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_callAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

/-- Positive part of underlying call value minus compound strike. -/
noncomputable def compoundCallOnCallAtChoice (m : BinomialMarket)
    (K L : ℝ) (postExerciseSteps : ℕ) (spot : ℝ) : ℝ :=
  max (callAtChoice m K postExerciseSteps spot - L) 0

end FinancialDerivatives.FD04


