-- Prove2me | Definitions.Def_actuarial_frUddSurvival
-- name    : actuarial_frUddSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:11:36.723745+00:00
-- url     : https://prove2.me/theorems/b68e907e-8233-4a78-bc30-f5ca1c031792
-- title:
--   Within-year survival and discount timing: frUddSurvival
-- statement:
--   UDD one-year conditional survival from the start of the year is the linear interpolant 1 minus the exposed fraction times annual death probability.
--
--   Mathematical relation:
--
--   $$
--   1 - s * q
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def frUddSurvival (q s : ℝ) : ℝ := 1 - s * q

end ActuarialValuation


