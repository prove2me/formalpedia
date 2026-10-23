-- Prove2me | Definitions.Def_actuarial_f_estateInstalment
-- name    : actuarial_f_estateInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-22T11:41:59.921055+00:00
-- url     : https://prove2.me/theorems/e74529d0-335f-4b45-85c0-b8b4b2af3a09
-- title:
--   Estate instalment
-- statement:
--   Estate instalment models a residual guarantee payable to an estate after member death. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^E_t(z,i)=K_zG^E_te_i(t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue

namespace ActuarialUnderpinsF
noncomputable def estateInstalment (h r g z i t : ℕ)
    (estateBase ge : ℕ → ℝ) : ℝ :=
  estateBase z * ge t * estateDue h r g i t
end ActuarialUnderpinsF


