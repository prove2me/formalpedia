-- Prove2me | Definitions.Def_actuarial_f_finalRounded
-- name    : actuarial_f_finalRounded
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:35:41.502112+00:00
-- url     : https://prove2.me/theorems/882ca2b6-65f6-4e39-ae3b-4e6373cc9c12
-- title:
--   Final rounded
-- statement:
--   Final rounded models an explicitly dated contractual pension amount or finite joint-life valuation. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   \mathcal R_{\rho,D}(x)=\rho D(x/\rho)\quad(\rho>0)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def finalRounded (x quantum : ℝ) (roundUnit : ℝ → ℝ) : ℝ :=
  if quantum ≤ 0 then x else quantum * roundUnit (x / quantum)

-- Rate floors and caps are applied first, then compounded per anniversary.
end ActuarialUnderpinsF


