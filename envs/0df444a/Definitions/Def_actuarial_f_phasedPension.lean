-- Prove2me | Definitions.Def_actuarial_f_phasedPension
-- name    : actuarial_f_phasedPension
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-22T06:53:53.250218+00:00
-- url     : https://prove2.me/theorems/f6bddc86-bd8e-4cc6-b3d7-6ef14772b0ea
-- title:
--   Phased pension
-- statement:
--   Phased pension models revaluation before retirement followed by a different in-payment increase stream. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   P_t=P_{\text{exit}}R_rQ_{r,t}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_deferredIncrease
import Definitions.Def_actuarial_f_paymentIncrease

namespace ActuarialUnderpinsF
noncomputable def phasedPension (base : ℝ) (r t : ℕ)
    (reval increase : ℕ → ℝ) : ℝ :=
  base * deferredIncrease r reval * paymentIncrease r t increase
end ActuarialUnderpinsF


