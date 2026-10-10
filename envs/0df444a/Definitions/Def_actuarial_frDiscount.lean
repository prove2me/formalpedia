-- Prove2me | Definitions.Def_actuarial_frDiscount
-- name    : actuarial_frDiscount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:20.912935+00:00
-- url     : https://prove2.me/theorems/5e2cf64a-54ef-4313-96ae-8ce4701684ed
-- title:
--   Within-year survival and discount timing: frDiscount
-- statement:
--   Discount at constant force of interest delta from time t to issue, with elapsed time in years.
--
--   Mathematical relation:
--
--   $$
--   Real.exp (-delta*t)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def frDiscount (delta t : ℝ) : ℝ := Real.exp (-delta*t)

end ActuarialValuation


