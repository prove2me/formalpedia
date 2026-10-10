-- Prove2me | Definitions.Def_actuarial_bnDiscount
-- name    : actuarial_bnDiscount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:45.047355+00:00
-- url     : https://prove2.me/theorems/5ed93984-a237-4905-b951-c3861f6ff288
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnDiscount
-- statement:
--   Value at issue of a one-year certain payment x with positive risk-free gross return R.
--
--   Mathematical relation:
--
--   $$
--   x/R
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnDiscount (R x : ℝ) : ℝ := x/R

end ActuarialValuation


