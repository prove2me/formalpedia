-- Prove2me | Definitions.Def_actuarial_bnOnePeriodPrice
-- name    : actuarial_bnOnePeriodPrice
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:02.912974+00:00
-- url     : https://prove2.me/theorems/3e933d4d-62e0-440b-8fcc-5eb0c0a118fd
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnOnePeriodPrice
-- statement:
--   Arbitrage-free candidate claim price from risk-neutral discounting under R>0 and q in (0,1).
--
--   Mathematical relation:
--
--   $$
--   bnExpectedPayoff q xu xd / R
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff

namespace ActuarialValuation

noncomputable def bnOnePeriodPrice (R q xu xd : ℝ) : ℝ := bnExpectedPayoff q xu xd / R

end ActuarialValuation


