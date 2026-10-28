-- Prove2me | Definitions.Def_actuarial_f_directEPV
-- name    : actuarial_f_directEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:32:09.310877+00:00
-- url     : https://prove2.me/theorems/244331fe-4522-4ef3-bacd-65bc2098fbda
-- title:
--   Direct e p v
-- statement:
--   Direct e p v models the scenario-first expected present value of actual member, spouse and estate instalments. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   V^{\text{direct}}=\sum_{z,i,j}p_{zij}V_{zij}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_realisedPV

namespace ActuarialUnderpinsF
noncomputable def directEPV (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate : ℕ → ℝ) (g0 g1 : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) : ℝ :=
  expect n h p (fun z i j => realisedPV h r g z i j disc a b c s estate g0 g1 gs ge)

-- Separately constructed streams preserve the correlation with the joint law.
end ActuarialUnderpinsF


