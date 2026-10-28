-- Prove2me | Definitions.Def_actuarial_f_firstAwardPV
-- name    : actuarial_f_firstAwardPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:34:53.00599+00:00
-- url     : https://prove2.me/theorems/f5c01800-ddd4-4759-8976-f5b1a411110d
-- title:
--   First award p v
-- statement:
--   First award p v models an irrevocably selected maximum at pension commencement. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   V_U=\sum_{z,i,j}p_{zij}\sum_tv_tU_zG_tm_i(t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), Chapter 20 (financial options), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_firstOptionPV

namespace ActuarialUnderpinsF
noncomputable def firstAwardPV (n h r : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b growth : ℕ → ℝ) : ℝ :=
  firstOptionPV n h r p disc (fun z => awardBase a b z) growth
end ActuarialUnderpinsF


