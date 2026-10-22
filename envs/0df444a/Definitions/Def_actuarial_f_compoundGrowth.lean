-- Prove2me | Definitions.Def_actuarial_f_compoundGrowth
-- name    : actuarial_f_compoundGrowth
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-21T06:06:56.473271+00:00
-- url     : https://prove2.me/theorems/a20d60d5-aff9-498e-882e-f81973e703fe
-- title:
--   Compound growth
-- statement:
--   Compound growth models compounded increases on the correct anniversary dates. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   G_t=\prod_{k=0}^{t-1}(1+\ell_k)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def compoundGrowth (r : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∏ k ∈ Finset.range t, (1 + r k)
end ActuarialUnderpinsF


