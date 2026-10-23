-- Prove2me | Definitions.Def_actuarial_f_survivorFlooredInstalment
-- name    : actuarial_f_survivorFlooredInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-22T11:41:47.983517+00:00
-- url     : https://prove2.me/theorems/08da150b-dfd2-49fa-a366-1719428b6365
-- title:
--   Survivor floored instalment
-- statement:
--   Survivor floored instalment models a survivor minimum fixed at member death followed by survivor-specific increases. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{S,\text{floor}}_t=\max(S^A_{zi},S^B_{zi})G^S_{i,t}s_{ij}(t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseBaseAtDeath
import Definitions.Def_actuarial_f_spouseDue

namespace ActuarialUnderpinsF
noncomputable def survivorFlooredInstalment (h z i j t : ℕ)
    (sa sb : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ) : ℝ :=
  spouseBaseAtDeath z i sa sb * gs i t * spouseDue h i j t
end ActuarialUnderpinsF


