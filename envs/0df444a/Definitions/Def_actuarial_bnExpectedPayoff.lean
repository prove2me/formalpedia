-- Prove2me | Definitions.Def_actuarial_bnExpectedPayoff
-- name    : actuarial_bnExpectedPayoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:52.466802+00:00
-- url     : https://prove2.me/theorems/fcfba83d-c0af-4e95-ac2f-b57139942adf
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnExpectedPayoff
-- statement:
--   Risk-neutral expected claim payoff given up- and down-state values at one period.
--
--   Mathematical relation:
--
--   $$
--   q*xu+(1-q)*xd
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnExpectedPayoff (q xu xd : ℝ) : ℝ := q*xu+(1-q)*xd

end ActuarialValuation


