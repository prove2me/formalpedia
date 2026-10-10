-- Prove2me | Definitions.Def_actuarial_frDueTerm
-- name    : actuarial_frDueTerm
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:45.340018+00:00
-- url     : https://prove2.me/theorems/071510fe-4b16-491f-aa02-06e9027f10bc
-- title:
--   Frequency-dependent annuity cashflow valuation: frDueTerm
-- statement:
--   A due payment at the beginning of subperiod j is payable on survival at that instant and carries one mth of the annual amount.
--
--   Mathematical relation:
--
--   $$
--   (c k / (m : ℝ)) * discount (frTime k j m) * p k * frUddSurvival (q k) ((j:ℝ)/(m:ℝ))
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frTime
import Definitions.Def_actuarial_frUddSurvival

namespace ActuarialValuation

noncomputable def frDueTerm (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (k j m : ℕ) : ℝ := (c k / (m : ℝ)) * discount (frTime k j m) * p k * frUddSurvival (q k) ((j:ℝ)/(m:ℝ))

end ActuarialValuation


