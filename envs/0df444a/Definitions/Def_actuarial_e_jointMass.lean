-- Prove2me | Definitions.Def_actuarial_e_jointMass
-- name    : actuarial_e_jointMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:04:11.283571+00:00
-- url     : https://prove2.me/theorems/8696a312-b6be-4d19-b60b-1824355d89e1
-- title:
--   Total joint mortality mass
-- statement:
--   Total joint mortality mass. Two discrete death-year indices, with the terminal cell denoting right-censoring.
--
--   The contractual and mortality relation is:
--
--   $$
--   \sum_{i=0}^{h}\sum_{j=0}^{h}p_{ij}
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Reused published Prove2Me Definition via a local symbol-preserving alias: ActuarialJointD.mass, UUID b00a8f74-66dd-46a8-aaf3-1b977b2355cc, from CII module Definitions.Def_actuarial_d_mass. Verified in a pinned private Prove2Me import compilation. Independent actuarial context: Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, p. 359, https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive

namespace ActuarialDeathE
noncomputable def jointMass (h : ℕ) (p : ℕ → ℕ → ℝ) : ℝ := ActuarialJointD.mass h p
end ActuarialDeathE


