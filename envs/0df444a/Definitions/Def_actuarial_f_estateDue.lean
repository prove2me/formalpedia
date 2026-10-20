-- Prove2me | Definitions.Def_actuarial_f_estateDue
-- name    : actuarial_f_estateDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-19T22:09:52.144305+00:00
-- url     : https://prove2.me/theorems/ccea8e18-c37f-46f9-b18f-f49091d0d52c
-- title:
--   Estate due
-- statement:
--   Estate due models a residual guarantee payable to an estate after member death. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   e_i(t)=\mathbf1_{\{r\le i<H,\ i<t<r+g\}}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def estateDue (h r g i t : ℕ) : ℝ :=
  if r ≤ i ∧ i < h ∧ i < t ∧ r ≤ t ∧ t < r + g then 1 else 0
end ActuarialUnderpinsF


