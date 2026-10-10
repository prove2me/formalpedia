-- Prove2me | solution 1 for ActuarialValuation.quotaShareCapitalObjective_expand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:05:58.723619+00:00
-- url     : https://prove2.me/submissions/f13f840f-22d8-474f-893b-634ea44bad59

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_quotaShareCapitalObjective
import Definitions.Def_actuarial_quotaShareVariancePremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q claim retention loading capital : ℝ) :
    quotaShareCapitalObjective q claim retention loading capital =
      q * claim + q * (1 - q) * claim ^ 2 *
        (loading * (1 - retention) ^ 2 + capital * retention ^ 2) := by
  dsimp [quotaShareCapitalObjective, quotaShareRetainedClaim,
    quotaShareVariancePremium, quotaShareCededClaim]
  ring
