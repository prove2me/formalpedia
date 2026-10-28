-- Prove2me | Definitions.Def_actuarial_f_lpiGrowth
-- name    : actuarial_f_lpiGrowth
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:35:56.05393+00:00
-- url     : https://prove2.me/theorems/2126a76d-9669-4e4f-a487-a0ffa3112a34
-- title:
--   Lpi growth
-- statement:
--   Lpi growth models one-year limited price increase, with the floor applied before the cap. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   G^{\text{LPI}}_t=\prod_{k=0}^{t-1}[1+\min(c,\max(f,\pi_k))]
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_compoundGrowth
import Definitions.Def_actuarial_f_lpiPath

namespace ActuarialUnderpinsF
noncomputable def lpiGrowth (floor cap : ℝ)
    (inflation : ℕ → ℝ) (t : ℕ) : ℝ :=
  compoundGrowth (lpiPath floor cap inflation) t

-- An estate guarantee may replace the spouse amount only on overlapping dates.
end ActuarialUnderpinsF


