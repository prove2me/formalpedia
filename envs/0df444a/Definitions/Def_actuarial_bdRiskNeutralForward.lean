-- Prove2me | Definitions.Def_actuarial_bdRiskNeutralForward
-- name    : actuarial_bdRiskNeutralForward
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:49.29399+00:00
-- url     : https://prove2.me/theorems/80fdf50e-ff99-4e25-bb26-25d03c21fe47
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdRiskNeutralForward
-- statement:
--   Zero-value forward delivery price using the state-price value of the delivery and the positive stochastic discount factor unit-bond value.
--
--   Mathematical relation:
--
--   $$
--   bdStatePV p discount delivery / bdStateZeroBond p discount
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV
import Definitions.Def_actuarial_bdStateZeroBond

namespace ActuarialValuation

noncomputable def bdRiskNeutralForward {m : ℕ} (p discount delivery : Fin m → ℝ) : ℝ := bdStatePV p discount delivery / bdStateZeroBond p discount

end ActuarialValuation


