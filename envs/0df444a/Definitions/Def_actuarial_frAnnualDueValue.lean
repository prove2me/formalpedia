-- Prove2me | Definitions.Def_actuarial_frAnnualDueValue
-- name    : actuarial_frAnnualDueValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:00.34588+00:00
-- url     : https://prove2.me/theorems/58b2190a-644c-4660-93e1-ef4e07e920ef
-- title:
--   Frequency-dependent annuity cashflow valuation: frAnnualDueValue
-- statement:
--   Annual due annuity with one payment at each integer anniversary k, including time zero.
--
--   Mathematical relation:
--
--   $$
--   ∑ k ∈ Finset.range n, c k * discount (k:ℝ) * p k
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def frAnnualDueValue (c : ℕ → ℝ) (discount : ℝ → ℝ) (p : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, c k * discount (k:ℝ) * p k

end ActuarialValuation


