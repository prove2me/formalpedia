-- Prove2me | Definitions.Def_actuarial_f_firstOptionPV
-- name    : actuarial_f_firstOptionPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:34:38.580908+00:00
-- url     : https://prove2.me/theorems/82dcb5e9-11a7-4071-9561-fe1c62c0d732
-- title:
--   First option p v
-- statement:
--   First option p v models the first tranche's pension award and one fixed future increase stream. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   V_A=\sum_{z,i,j}p_{zij}\sum_tv_tA_zG_tm_i(t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), Chapter 20 (financial options), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_memberDue

namespace ActuarialUnderpinsF
noncomputable def firstOptionPV (n h r : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc base growth : ℕ → ℝ) : ℝ :=
  expect n h p (fun z i j =>
    ∑ t ∈ Finset.range (h + 1), disc t * (base z * growth t * memberDue r i t))
end ActuarialUnderpinsF


