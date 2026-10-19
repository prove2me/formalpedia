-- Prove2me | Definitions.Def_actuarial_e_alive
-- name    : actuarial_e_alive
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:04:55.96799+00:00
-- url     : https://prove2.me/theorems/0028c3ba-5f75-47a3-9b98-73a30ce7f062
-- title:
--   Alive on an anniversary
-- statement:
--   Alive on an anniversary. Member or dependent remains alive on tick t exactly when its death-year index is at least t.
--
--   The contractual and mortality relation is:
--
--   $$
--   A(i,t)=\mathbf{1}_{\{t\leq i\}}
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Reused published Prove2Me Definition via a local symbol-preserving alias: ActuarialJointD.alive, UUID a91b7884-a090-4090-983e-06c2c8139437, from CII module Definitions.Def_actuarial_d_alive. Verified in a pinned private Prove2Me import compilation. Independent actuarial context: Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, p. 359, https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive

namespace ActuarialDeathE
noncomputable def alive (i t : ℕ) : ℝ := ActuarialJointD.alive i t
end ActuarialDeathE


