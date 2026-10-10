-- Prove2me | Definitions.Def_actuarial_frTime
-- name    : actuarial_frTime
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:28.417233+00:00
-- url     : https://prove2.me/theorems/3b12a4b4-3c75-4e17-b7f0-9db0bd50d8a5
-- title:
--   Within-year survival and discount timing: frTime
-- statement:
--   Payment time measured from issue: integer policy year k plus j of m subannual periods.
--
--   Mathematical relation:
--
--   $$
--   (k : ℝ) + (j : ℝ) / (m : ℝ)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def frTime (k j m : ℕ) : ℝ := (k : ℝ) + (j : ℝ) / (m : ℝ)

end ActuarialValuation


