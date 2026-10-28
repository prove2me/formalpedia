-- Prove2me | Definitions.Def_actuarial_f_trancheFloorTotal
-- name    : actuarial_f_trancheFloorTotal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:35:07.06211+00:00
-- url     : https://prove2.me/theorems/8f0e5f58-fe42-4d31-b431-9f61eb6f8e8e
-- title:
--   Tranche floor total
-- statement:
--   Tranche floor total models minimum rights evaluated for each pension tranche, rather than the aggregate. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   U_{\text{tranche}}=\sum_{k=1}^K\max(A_k,B_k)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase

namespace ActuarialUnderpinsF
noncomputable def trancheFloorTotal (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, awardBase a b i
end ActuarialUnderpinsF


