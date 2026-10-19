-- Prove2me | Definitions.Def_actuarial_e_spousePayment
-- name    : actuarial_e_spousePayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:31:35.408553+00:00
-- url     : https://prove2.me/theorems/6a4f9480-3004-48bf-a32c-eceb33491ffd
-- title:
--   Survivor pension with entitlement fixed at death
-- statement:
--   Survivor pension with entitlement fixed at death. Active, deferred and retired bases crystallise at death; replacement suspends only a retiree's survivor pension inside the guarantee.
--
--   The contractual and mortality relation is:
--
--   $$
--   R_t(i,j;\eta)=S(i,j,t)u_t\bigl(I_Aa_{i+1}+I_Db'_{i+1}+I_Rc_{i+1}\mathbf{1}_{\{\eta=0\ \lor\ t\geq r+g\}}\bigr)
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 10, p. 388, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_active
import Definitions.Def_actuarial_e_deferred
import Definitions.Def_actuarial_e_retired
import Definitions.Def_actuarial_e_spouseDue

namespace ActuarialDeathE
noncomputable def spousePayment (h e r g i j t : ℕ) (activeBasis deferredBasis retiredBasis increase : ℕ → ℝ) (replace : Bool) : ℝ := spouseDue i j t * increase t * (active h e i * activeBasis (i + 1) + deferred h e r i * deferredBasis (i + 1) + retired h r i * retiredBasis (i + 1) * (if replace ∧ t < r + g then (0 : ℝ) else 1))
end ActuarialDeathE


