-- Prove2me | Definitions.Def_OutcomeRebate_Transfer_Supplement_UniformPrices
-- name    : OutcomeRebate_Transfer_Supplement_UniformPrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:00:24.187573+00:00
-- url     : https://prove2.me/theorems/a5ae32b5-77c1-465d-9be2-1845aa3f1714
-- title:
--   §3.1.3 — uncovered uniform-pricing interior price
-- statement:
--   Let $c$ be unit production cost, $\bar v$ the upper patient value and $z=1+(\lambda(1-q)/q)^{1/\alpha}$ the published uniform-pricing risk multiplier. Define the uncovered interior price by
--
--   $$\bar p^*=c/2+\bar v/(2z).$$
--
--   The published model supplies the patient and payer objectives, profit and equilibrium predicate. This file adds only the missing candidate price; it does not identify that candidate with an equilibrium.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 16 (PDF 17), §3.1.3

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer.Supplement

/-- Uncovered interior optimum, §3.1.3, printed p.16. -/
noncomputable def pBarStar (P : Params) : ℝ := P.c / 2 + P.vbar / (2 * P.z)

end OutcomeRebate.Transfer.Supplement


