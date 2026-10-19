-- Prove2me | Definitions.Def_actuarial_e_instalmentScheduled
-- name    : actuarial_e_instalmentScheduled
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:36:17.108066+00:00
-- url     : https://prove2.me/theorems/053cbb4b-6552-4bd0-ac32-52ac37a03e29
-- title:
--   Frequency-adjusted payment
-- statement:
--   Frequency-adjusted payment. The time unit and benefit amount per instalment must be fixed independently of the selector.
--
--   The contractual and mortality relation is:
--
--   $$
--   C^{(m)}_t=H_m(t)\,C_t
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 11, p. 423, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_instalment
import Definitions.Def_actuarial_e_scheduled

namespace ActuarialDeathE
noncomputable def instalmentScheduled (m h e r g i j t : ℕ) (base a b c increase : ℕ → ℝ) (replace : Bool) : ℝ := scheduled m t * instalment h e r g i j t base a b c increase replace
end ActuarialDeathE


