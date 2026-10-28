-- Prove2me | Definitions.Def_actuarial_f_stateEPV
-- name    : actuarial_f_stateEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:32:21.224854+00:00
-- url     : https://prove2.me/theorems/48ebe465-1aa0-4447-b5d9-0c8983b23dac
-- title:
--   State e p v
-- statement:
--   State e p v models the payment-date aggregation of separately defined benefit states. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   V^{\text{state}}=\sum_{t=0}^Hv_t\sum_{z,i,j}p_{zij}C_t(z,i,j)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseInstalment

namespace ActuarialUnderpinsF
noncomputable def stateEPV (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate : ℕ → ℝ) (g0 g1 : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (h + 1), disc t * (
    g0 t * expect n h p (fun z i j => awardBase a b z * memberDue r i t) +
    g1 t * expect n h p (fun z i j => c z * memberDue r i t) +
    expect n h p (fun z i j => spouseInstalment h z i j t s gs) +
    ge t * expect n h p (fun z i j => estate z * estateDue h r g i t))
end ActuarialUnderpinsF


