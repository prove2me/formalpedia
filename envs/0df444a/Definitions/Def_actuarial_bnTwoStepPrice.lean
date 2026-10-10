-- Prove2me | Definitions.Def_actuarial_bnTwoStepPrice
-- name    : actuarial_bnTwoStepPrice
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:23.333099+00:00
-- url     : https://prove2.me/theorems/fc901fcc-902c-466e-b8e6-315461637f91
-- title:
--   Two-period binomial recursion and American option exercise: bnTwoStepPrice
-- statement:
--   Two-period binomial discounted expected payoff over four ordered paths, preserving path-dependent middle nodes.
--
--   Mathematical relation:
--
--   $$
--   (q*q*uu+q*(1-q)*ud+(1-q)*q*du+(1-q)*(1-q)*dd)/(R*R)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def bnTwoStepPrice (R q uu ud du dd : ℝ) : ℝ := (q*q*uu+q*(1-q)*ud+(1-q)*q*du+(1-q)*(1-q)*dd)/(R*R)

end ActuarialValuation


