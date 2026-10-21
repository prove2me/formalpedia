-- Prove2me | Definitions.Def_actuarial_f_annualFloorPayment
-- name    : actuarial_f_annualFloorPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-20T06:41:25.983966+00:00
-- url     : https://prove2.me/theorems/e9f4761f-5f75-4778-9a37-909fb42742df
-- title:
--   Annual floor payment
-- statement:
--   Annual floor payment models a new contractual floor comparison at each payment anniversary. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   F^{\text{annual}}_{zt}=\max(A_zG^A_t,B_zG^B_t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def annualFloorPayment (a b : ℕ → ℝ)
    (ga gb : ℕ → ℝ) (z t : ℕ) : ℝ :=
  max (a z * ga t) (b z * gb t)
end ActuarialUnderpinsF


