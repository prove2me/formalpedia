-- Prove2me | Definitions.Def_actuarial_frDueValue
-- name    : actuarial_frDueValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:23.061543+00:00
-- url     : https://prove2.me/theorems/4b092d0f-9691-44ad-b340-6f3357954c9b
-- title:
--   Frequency-dependent annuity cashflow valuation: frDueValue
-- statement:
--   The finite n-year m-thly due annuity value discounts and weights each start-of-subperiod payment separately.
--
--   Mathematical relation:
--
--   $$
--   ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, frDueTerm c discount p q k j m
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueTerm

namespace ActuarialValuation

noncomputable def frDueValue (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) : ℝ := ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, frDueTerm c discount p q k j m

end ActuarialValuation


