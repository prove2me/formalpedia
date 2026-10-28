-- Prove2me | Definitions.Def_actuarial_f_wholeFloorTotal
-- name    : actuarial_f_wholeFloorTotal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:35:15.441472+00:00
-- url     : https://prove2.me/theorems/a7748d5c-d097-4622-bf9f-ecbba7155895
-- title:
--   Whole floor total
-- statement:
--   Whole floor total models a minimum applied after adding the pensions across tranches. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   U_{\text{whole}}=\max\left(\sum_{k=1}^KA_k,\sum_{k=1}^KB_k\right)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def wholeFloorTotal (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  max (∑ i ∈ Finset.range k, a i) (∑ i ∈ Finset.range k, b i)
end ActuarialUnderpinsF


