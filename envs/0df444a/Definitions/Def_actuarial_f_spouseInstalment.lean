-- Prove2me | Definitions.Def_actuarial_f_spouseInstalment
-- name    : actuarial_f_spouseInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-22T07:08:21.135663+00:00
-- url     : https://prove2.me/theorems/593014a0-42a7-4677-b3cb-ec9baa60dc27
-- title:
--   Spouse instalment
-- statement:
--   Spouse instalment models survivor pension entitlement determined at member death. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{S}_t(z,i,j)=S_{zi}G^{S}_{i,t}s_{ij}(t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

namespace ActuarialUnderpinsF
noncomputable def spouseInstalment (h z i j t : ℕ)
    (spouseBase : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ) : ℝ :=
  spouseBase z i * gs i t * spouseDue h i j t
end ActuarialUnderpinsF


