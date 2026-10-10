-- Prove2me | Definitions.Def_actuarial_pvTermBenefit
-- name    : actuarial_pvTermBenefit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:53.960985+00:00
-- url     : https://prove2.me/theorems/3c6849a6-f066-436b-bab9-8de9b9c5d424
-- title:
--   Finite random present values of insurance benefits and premium streams: pvTermBenefit
-- statement:
--   Term assurance pays for deaths in years k strictly before term and discounts each paid benefit to the end of death year.
--
--   Mathematical relation:
--
--   $$
--   if k < term then benefit k * discount (k+1) else 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvTermBenefit (benefit discount : ℕ → ℝ) (term k : ℕ) : ℝ := if k < term then benefit k * discount (k+1) else 0

end ActuarialValuation


