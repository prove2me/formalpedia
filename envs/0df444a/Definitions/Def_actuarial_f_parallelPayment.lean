-- Prove2me | Definitions.Def_actuarial_f_parallelPayment
-- name    : actuarial_f_parallelPayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-22T11:42:17.144051+00:00
-- url     : https://prove2.me/theorems/70f68762-d095-4490-924a-eaf4407bfb0b
-- title:
--   Parallel payment
-- statement:
--   Parallel payment models independent spouse and guaranteed estate payments under a parallel contract. The formula specifies the actual due-date basis and contractual beneficiary or indexation conditions.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{\text{par}}_t=C^S_t+C^E_t
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_spouseInstalment

namespace ActuarialUnderpinsF
noncomputable def parallelPayment (h r g z i j t : ℕ)
    (spouseBase : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (estateBase ge : ℕ → ℝ) : ℝ :=
  spouseInstalment h z i j t spouseBase gs +
    estateInstalment h r g z i t estateBase ge
end ActuarialUnderpinsF


