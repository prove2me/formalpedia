-- Prove2me | Definitions.Def_actuarial_e_spouseDueImmediate
-- name    : actuarial_e_spouseDueImmediate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:56:41.530987+00:00
-- url     : https://prove2.me/theorems/a7fdd10e-17cb-4e8e-bec9-30c3a54240e7
-- title:
--   Alternative immediate survivor commencement
-- statement:
--   Alternative immediate survivor commencement. The first survivor payment may fall on the death settlement anniversary when the contract grants that entitlement.
--
--   The contractual and mortality relation is:
--
--   $$
--   S_{\text{immediate}}(i,j,t)=\mathbf{1}_{\{i<j,\ i<t\leq j\}}
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Reused published Prove2Me Definition via an original local API alias: ActuarialJointD.onlyY, UUID 72df404e-d88d-4e63-ad53-1046a3a9e354, from Foundation D. Targeted compiled import Definitions.Def_actuarial_d_onlyY at the pinned Mathlib revision. The E settlement-delayed spouseDue remains a separate contract rule. Independent actuarial context: Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, p. 388, https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive

namespace ActuarialDeathE
noncomputable def spouseDueImmediate (i j t : ℕ) : ℝ := ActuarialJointD.onlyY i j t
end ActuarialDeathE


