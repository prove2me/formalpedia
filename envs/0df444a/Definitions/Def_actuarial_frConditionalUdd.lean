-- Prove2me | Definitions.Def_actuarial_frConditionalUdd
-- name    : actuarial_frConditionalUdd
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:02.834468+00:00
-- url     : https://prove2.me/theorems/4ee87a85-72e0-438c-ab91-cdc0491c91c7
-- title:
--   Within-year survival and discount timing: frConditionalUdd
-- statement:
--   UDD survival conditional on being alive s years after an anniversary and continuing another t years requires a positive survival denominator.
--
--   Mathematical relation:
--
--   $$
--   frUddSurvival q (s+t) / frUddSurvival q s
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival

namespace ActuarialValuation

noncomputable def frConditionalUdd (q s t : ℝ) : ℝ := frUddSurvival q (s+t) / frUddSurvival q s

end ActuarialValuation


