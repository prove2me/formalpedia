-- Prove2me | Definitions.Def_actuarial_f_realisedPV
-- name    : actuarial_f_realisedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:26:22.920016+00:00
-- url     : https://prove2.me/theorems/12031777-62f5-4572-b7bf-1020b4181c76
-- title:
--   Realised p v
-- statement:
--   Realised p v models an explicitly dated contractual pension amount or finite joint-life valuation. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   V_{zij}=\sum_{t=0}^Hv_tC_t(z,i,j)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_totalInstalment

namespace ActuarialUnderpinsF
noncomputable def realisedPV (h r g z i j : ℕ) (disc : ℕ → ℝ)
    (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ) (estate : ℕ → ℝ)
    (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (h + 1),
    disc t * totalInstalment h r g z i j t a b c s estate g0 g1 gs ge
end ActuarialUnderpinsF


