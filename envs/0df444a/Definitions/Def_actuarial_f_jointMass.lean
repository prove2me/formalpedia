-- Prove2me | Definitions.Def_actuarial_f_jointMass
-- name    : actuarial_f_jointMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-19T12:55:31.124001+00:00
-- url     : https://prove2.me/theorems/5b022b9b-65aa-4dc2-89ad-2222da8eb287
-- title:
--   Joint mass
-- statement:
--   Joint mass models an explicitly dated contractual pension amount or finite joint-life valuation. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   \sum_{z,i,j}p_{zij}
--   $$
--
--   The formal definition delegates its two-life kernel to the published CII module, with F-specific award-state, retirement and censoring conditions retained.
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page. Reuses CII published actuarial_d_mass; award-state sum of published joint death-law masses. External import must be verified in the exact pinned environment.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Definitions.Def_actuarial_d_mass

namespace ActuarialUnderpinsF
noncomputable def jointMass (n h : ℕ) (p : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ z ∈ Finset.range n, ActuarialJointD.mass h (fun i j => p z i j)
end ActuarialUnderpinsF


