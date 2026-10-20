-- Prove2me | Definitions.Def_actuarial_f_fixedChoicePayment
-- name    : actuarial_f_fixedChoicePayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-19T22:11:34.454184+00:00
-- url     : https://prove2.me/theorems/efc75538-c654-49ef-847c-59e216c66278
-- title:
--   Fixed choice payment
-- statement:
--   Fixed choice payment models a once-selected award alternative with its own subsequent increase path. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   F_{zt}=A_zG^A_t\mathbf1_{\{A_z>B_z\}}+B_zG^B_t\mathbf1_{\{A_z\le B_z\}}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def fixedChoicePayment (a b : ℕ → ℝ)
    (ga gb : ℕ → ℝ) (z t : ℕ) : ℝ :=
  if a z ≤ b z then b z * gb t else a z * ga t

-- A fresh comparison on every payment date is a different contract.
end ActuarialUnderpinsF


