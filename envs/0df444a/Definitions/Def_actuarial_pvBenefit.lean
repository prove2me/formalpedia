-- Prove2me | Definitions.Def_actuarial_pvBenefit
-- name    : actuarial_pvBenefit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:26.825006+00:00
-- url     : https://prove2.me/theorems/be090d37-015c-4527-a933-d03b398e3712
-- title:
--   Finite random present values of insurance benefits and premium streams: pvBenefit
-- statement:
--   The random benefit present value for a realised finite scenario is the scenario benefit discounted at its precise event date.
--
--   Mathematical relation:
--
--   $$
--   benefit i * discount i
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvBenefit {n : ℕ} (benefit discount : Fin n → ℝ) (i : Fin n) : ℝ := benefit i * discount i

end ActuarialValuation


