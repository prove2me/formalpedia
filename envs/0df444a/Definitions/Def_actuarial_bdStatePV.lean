-- Prove2me | Definitions.Def_actuarial_bdStatePV
-- name    : actuarial_bdStatePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:04.472712+00:00
-- url     : https://prove2.me/theorems/451df791-0325-415f-bc8c-b4dbd2329f2f
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdStatePV
-- statement:
--   Actual finite-scenario stochastic discount-factor valuation with nonnegative state weights, stochastic discount factors and contract payoffs.
--
--   Mathematical relation:
--
--   $$
--   ∑ ω : Fin m, p ω * discount ω * payoff ω
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def bdStatePV {m : ℕ} (p discount payoff : Fin m → ℝ) : ℝ := ∑ ω : Fin m, p ω * discount ω * payoff ω

end ActuarialValuation


