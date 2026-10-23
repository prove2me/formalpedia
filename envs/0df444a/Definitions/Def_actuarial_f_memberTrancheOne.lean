-- Prove2me | Definitions.Def_actuarial_f_memberTrancheOne
-- name    : actuarial_f_memberTrancheOne
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-22T06:54:04.54002+00:00
-- url     : https://prove2.me/theorems/a08c409a-583a-474d-bac5-fb62a020c40c
-- title:
--   Member tranche one
-- statement:
--   Member tranche one models member pension instalments payable only while alive after commencement. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{(1)}_t(z,i)=U_zG^{(1)}_tm_i(t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_memberDue

namespace ActuarialUnderpinsF
noncomputable def memberTrancheOne (r z i t : ℕ)
    (a b : ℕ → ℝ) (g0 : ℕ → ℝ) : ℝ :=
  awardBase a b z * g0 t * memberDue r i t
end ActuarialUnderpinsF


