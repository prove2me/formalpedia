-- Prove2me | Definitions.Def_actuarial_f_bridgeDue
-- name    : actuarial_f_bridgeDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:35:22.994594+00:00
-- url     : https://prove2.me/theorems/72166d4e-b192-497b-889f-7ac4b1c70d6e
-- title:
--   Bridge due
-- statement:
--   Bridge due models an extra temporary pension stopping at the specified cessation anniversary. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   b(t)=\mathbf1_{\{t_{\text{start}}\le t<t_{\text{stop}}\}}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def bridgeDue (start stop t : ℕ) : ℝ :=
  if start ≤ t ∧ t < stop then 1 else 0
end ActuarialUnderpinsF


