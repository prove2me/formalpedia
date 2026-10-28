-- Prove2me | Definitions.Def_actuarial_f_guaranteeOverlapEPV
-- name    : actuarial_f_guaranteeOverlapEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:36:45.454226+00:00
-- url     : https://prove2.me/theorems/3d7060a6-5f8a-44b1-bf4a-aa7f2ecf7954
-- title:
--   Guarantee overlap e p v
-- statement:
--   Guarantee overlap e p v models exclusive expiry of the estate guarantee and its interaction with a spouse benefit. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   O=\mathbb E_p[\sum_tv_tC^S_t\mathbf1_{\{e_i(t)=1\}}]
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_spouseInstalment

namespace ActuarialUnderpinsF
noncomputable def guaranteeOverlapEPV (n h r g : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc : ℕ → ℝ)
    (s gs : ℕ → ℕ → ℝ) : ℝ :=
  expect n h p (fun z i j =>
    ∑ t ∈ Finset.range (h + 1), disc t *
      (if estateDue h r g i t = 1 then
        spouseInstalment h z i j t s gs else 0))

-- A bridging payment is a separate temporary component of the same contract.
end ActuarialUnderpinsF


