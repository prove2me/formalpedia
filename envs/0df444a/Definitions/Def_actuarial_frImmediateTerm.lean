-- Prove2me | Definitions.Def_actuarial_frImmediateTerm
-- name    : actuarial_frImmediateTerm
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:03.50399+00:00
-- url     : https://prove2.me/theorems/fff2670a-084e-4a59-bf79-b5836689db1b
-- title:
--   Frequency-dependent annuity cashflow valuation: frImmediateTerm
-- statement:
--   An immediate payment is due at the end of subperiod j and requires survival through that precise endpoint.
--
--   Mathematical relation:
--
--   $$
--   (c k / (m : ℝ)) * discount (frTime k (j+1) m) * p k * frUddSurvival (q k) (((j:ℝ)+1)/(m:ℝ))
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

noncomputable def frImmediateTerm (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (k j m : ℕ) : ℝ := (c k / (m : ℝ)) * discount (frTime k (j+1) m) * p k * frUddSurvival (q k) (((j:ℝ)+1)/(m:ℝ))

end ActuarialValuation


