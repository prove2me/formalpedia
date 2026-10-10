-- Prove2me | Definitions.Def_actuarial_bnRiskNeutralDown
-- name    : actuarial_bnRiskNeutralDown
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:37.294979+00:00
-- url     : https://prove2.me/theorems/c72ba38e-9a0e-4ccc-9bef-e08fa0e2fb07
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnRiskNeutralDown
-- statement:
--   Down-state risk-neutral probability is the complement of up-state probability under a valid no-arbitrage ordering.
--
--   Mathematical relation:
--
--   $$
--   1-bnRiskNeutralProb u d R
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb

namespace ActuarialValuation

noncomputable def bnRiskNeutralDown (u d R : ℝ) : ℝ := 1-bnRiskNeutralProb u d R

end ActuarialValuation


