-- Prove2me | Definitions.Def_OutcomeRebate_Transfer_Supplement_OutcomePrices
-- name    : OutcomeRebate_Transfer_Supplement_OutcomePrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:00:46.966537+00:00
-- url     : https://prove2.me/theorems/ac6f28b1-a4eb-449a-a311-726d1eed9c5a
-- title:
--   §3.2.3 — uncovered outcome-based interior price
-- statement:
--   Let $c$ be production cost, $q$ the probability of success and $\bar v$ the upper patient value. Define the uncovered interior price by
--
--   $$\hat p^*=c/(2q)+\bar v/2.$$
--
--   The published outcome-based model supplies demand, objectives, profit and the maximization predicate. This definition is a candidate price, whose optimality is a theorem conclusion.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 19 (PDF 20), §3.2.3

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer.Supplement

/-- Uncovered interior optimum, §3.2.3, printed p.19. -/
noncomputable def pHatStar (P : Params) : ℝ := P.c / (2 * P.q) + P.vbar / 2

end OutcomeRebate.Transfer.Supplement


