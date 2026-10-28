-- Prove2me | Definitions.Def_actuarial_f_totalInstalment
-- name    : actuarial_f_totalInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:25:54.658628+00:00
-- url     : https://prove2.me/theorems/226719d0-2d3a-4a70-8ca5-148274a6c9ca
-- title:
--   Total instalment
-- statement:
--   Total instalment models the complete benefit package built from independent entitlement indicators. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   C_t=C^{(1)}_t+C^{(2)}_t+C^S_t+C^E_t
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_memberTrancheOne
import Definitions.Def_actuarial_f_memberTrancheTwo
import Definitions.Def_actuarial_f_spouseInstalment

namespace ActuarialUnderpinsF
noncomputable def totalInstalment (h r g z i j t : ℕ)
    (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ) (estate : ℕ → ℝ)
    (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) : ℝ :=
  memberTrancheOne r z i t a b g0 +
    memberTrancheTwo r z i t c g1 +
    spouseInstalment h z i j t s gs +
    estateInstalment h r g z i t estate ge
end ActuarialUnderpinsF


