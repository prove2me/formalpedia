-- Prove2me | Definitions.Def_actuarial_frForceSurvival
-- name    : actuarial_frForceSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:11:45.556994+00:00
-- url     : https://prove2.me/theorems/fdb23a7d-1fc0-4311-9bbd-0c0ad19e710d
-- title:
--   Within-year survival and discount timing: frForceSurvival
-- statement:
--   Constant-force within-year survival uses the exponential of minus force times elapsed duration; force has units inverse years.
--
--   Mathematical relation:
--
--   $$
--   Real.exp (-mu * s)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def frForceSurvival (mu s : ℝ) : ℝ := Real.exp (-mu * s)

end ActuarialValuation


