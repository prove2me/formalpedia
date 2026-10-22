-- Prove2me | Definitions.Def_actuarial_f_additiveGrowth
-- name    : actuarial_f_additiveGrowth
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-21T06:07:05.195759+00:00
-- url     : https://prove2.me/theorems/8c8bbd29-8e9a-4730-88c5-2350ca6584a2
-- title:
--   Additive growth
-- statement:
--   Additive growth models an explicitly dated contractual pension amount or finite joint-life valuation. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   G^{\text{add}}_t=1+\sum_{k=0}^{t-1}\ell_k
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def additiveGrowth (r : ℕ → ℝ) (t : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range t, r k
end ActuarialUnderpinsF


