-- Prove2me | Definitions.Def_actuarial_e_validLaw
-- name    : actuarial_e_validLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:04:28.544524+00:00
-- url     : https://prove2.me/theorems/fbab4878-84c2-4e0e-a746-00aa8a5f3531
-- title:
--   Nonnegative normalised dependent-life law
-- statement:
--   Nonnegative normalised dependent-life law. The joint distribution may contain positive probability of same-year death; independence is optional.
--
--   The contractual and mortality relation is:
--
--   $$
--   p_{ij}\geq 0,\quad\sum_{i,j}p_{ij}=1
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Reused published Prove2Me Definition via a local symbol-preserving alias: ActuarialJointD.valid, UUID bd630584-12e6-47df-b270-aef694503595, from CII module Definitions.Def_actuarial_d_valid. Verified in a pinned private Prove2Me import compilation. Independent actuarial context: Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, p. 359, https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive

namespace ActuarialDeathE
noncomputable def validLaw (h : ℕ) (p : ℕ → ℕ → ℝ) : Prop := ActuarialJointD.valid h p
end ActuarialDeathE


