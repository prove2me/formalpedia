-- Prove2me | Definitions.Def_actuarial_e_instalment
-- name    : actuarial_e_instalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:32:22.730527+00:00
-- url     : https://prove2.me/theorems/ae012e9d-bbfb-4a09-8a6c-ea1262be4125
-- title:
--   Combined instalment after member death
-- statement:
--   Combined instalment after member death. The estate guarantee and the survivor pension can coexist or be coordinated by a replacement switch.
--
--   The contractual and mortality relation is:
--
--   $$
--   C_t(i,j;\eta)=M_t(i)+R_t(i,j;\eta)+G_t(i)
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
import Definitions.Def_actuarial_e_memberPayment
import Definitions.Def_actuarial_e_guaranteePayment
import Definitions.Def_actuarial_e_spousePayment

namespace ActuarialDeathE
noncomputable def instalment (h e r g i j t : ℕ) (base activeBasis deferredBasis retiredBasis increase : ℕ → ℝ) (replace : Bool) : ℝ := memberPayment r i t base + spousePayment h e r g i j t activeBasis deferredBasis retiredBasis increase replace + guaranteePayment h r g i t base
end ActuarialDeathE


