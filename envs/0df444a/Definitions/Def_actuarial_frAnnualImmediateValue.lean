-- Prove2me | Definitions.Def_actuarial_frAnnualImmediateValue
-- name    : actuarial_frAnnualImmediateValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:19.134494+00:00
-- url     : https://prove2.me/theorems/b387abfa-eabe-4cb7-bfb0-add04ad967d0
-- title:
--   Frequency-dependent annuity cashflow valuation: frAnnualImmediateValue
-- statement:
--   Annual immediate annuity has one payment at integer times k plus one, requiring survival through year end.
--
--   Mathematical relation:
--
--   $$
--   ∑ k ∈ Finset.range n, c k * discount ((k:ℝ)+1) * p (k+1)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def frAnnualImmediateValue (c : ℕ → ℝ) (discount : ℝ → ℝ) (p : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, c k * discount ((k:ℝ)+1) * p (k+1)

end ActuarialValuation


