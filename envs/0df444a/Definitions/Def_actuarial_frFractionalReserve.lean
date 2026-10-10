-- Prove2me | Definitions.Def_actuarial_frFractionalReserve
-- name    : actuarial_frFractionalReserve
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:51.546158+00:00
-- url     : https://prove2.me/theorems/98261d7c-edea-4076-9e5e-c86dda87a638
-- title:
--   Fractional premiums and policy reserves: frFractionalReserve
-- statement:
--   Conditional reserve s years after the anniversary with premium paid at the anniversary, accumulation to s and death benefit payable at the end of the policy year; mortality follows UDD.
--
--   Mathematical relation:
--
--   $$
--   ((assets + premium) * growth - s*q*benefit*endDiscount) / frUddSurvival q s
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival

namespace ActuarialValuation

noncomputable def frFractionalReserve (assets premium benefit q s growth endDiscount : ℝ) : ℝ := ((assets + premium) * growth - s*q*benefit*endDiscount) / frUddSurvival q s

end ActuarialValuation


