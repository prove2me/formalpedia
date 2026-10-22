-- Prove2me | Definitions.Def_actuarial_f_deferredIncrease
-- name    : actuarial_f_deferredIncrease
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-21T11:26:27.974282+00:00
-- url     : https://prove2.me/theorems/e0e82a40-2a6f-429a-a295-549dd8c795f6
-- title:
--   Deferred increase
-- statement:
--   Deferred increase models a preserved pension revalued up to retirement. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   R_r=\prod_{k=0}^{r-1}(1+\ell^{D}_k)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_compoundGrowth

namespace ActuarialUnderpinsF
noncomputable def deferredIncrease (r : ℕ) (reval : ℕ → ℝ) : ℝ :=
  compoundGrowth reval r
end ActuarialUnderpinsF


