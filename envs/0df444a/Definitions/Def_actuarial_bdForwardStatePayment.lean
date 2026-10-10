-- Prove2me | Definitions.Def_actuarial_bdForwardStatePayment
-- name    : actuarial_bdForwardStatePayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:30.798556+00:00
-- url     : https://prove2.me/theorems/997ef2e7-b326-4ac8-8358-336a392ea39a
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdForwardStatePayment
-- statement:
--   State-price value of a forward payoff delivering a state-contingent bond value less deterministic delivery price K.
--
--   Mathematical relation:
--
--   $$
--   bdStatePV p discount (fun ω => delivery ω - K)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV

namespace ActuarialValuation

noncomputable def bdForwardStatePayment {m : ℕ} (p discount delivery : Fin m → ℝ) (K : ℝ) : ℝ := bdStatePV p discount (fun ω => delivery ω - K)

end ActuarialValuation


