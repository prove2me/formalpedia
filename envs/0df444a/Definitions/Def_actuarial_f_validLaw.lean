-- Prove2me | Definitions.Def_actuarial_f_validLaw
-- name    : actuarial_f_validLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-19T12:55:41.665858+00:00
-- url     : https://prove2.me/theorems/99a2ac28-cdc8-440b-8442-70c718ba68e8
-- title:
--   Valid law
-- statement:
--   Valid law models an explicitly dated contractual pension amount or finite joint-life valuation. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   p_{zij}\ge0,\qquad\sum_{z,i,j}p_{zij}=1
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_jointMass

namespace ActuarialUnderpinsF
noncomputable def validLaw (n h : ℕ) (p : ℕ → ℕ → ℕ → ℝ) : Prop :=
  0 < n ∧ (∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h + 1),
    ∀ j ∈ Finset.range (h + 1), 0 ≤ p z i j) ∧ jointMass n h p = 1
end ActuarialUnderpinsF


