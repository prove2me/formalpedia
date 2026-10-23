-- Prove2me | Definitions.Def_actuarial_f_memberTrancheTwo
-- name    : actuarial_f_memberTrancheTwo
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-22T06:54:26.102111+00:00
-- url     : https://prove2.me/theorems/dad8e1a3-655f-4c29-ac7a-e492cd0fa08c
-- title:
--   Member tranche two
-- statement:
--   Member tranche two models member pension instalments payable only while alive after commencement. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{(2)}_t(z,i)=C_zG^{(2)}_tm_i(t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue

namespace ActuarialUnderpinsF
noncomputable def memberTrancheTwo (r z i t : ℕ)
    (c g1 : ℕ → ℝ) : ℝ :=
  c z * g1 t * memberDue r i t

-- The spouse basis is indexed by member death year i, never future payment t.
end ActuarialUnderpinsF


