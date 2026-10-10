-- Prove2me | Definitions.Def_actuarial_pvEndowmentBenefit
-- name    : actuarial_pvEndowmentBenefit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:03.544558+00:00
-- url     : https://prove2.me/theorems/e118ac45-93a4-4e10-87a0-013ea7f05e9e
-- title:
--   Finite random present values of insurance benefits and premium streams: pvEndowmentBenefit
-- statement:
--   Endowment insurance pays discounted death benefit on an earlier death event, otherwise pays the predetermined discounted maturity benefit.
--
--   Mathematical relation:
--
--   $$
--   if beforeMaturity then death else maturityDiscount
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvEndowmentBenefit (death maturityDiscount : ℝ) (beforeMaturity : Prop) [Decidable beforeMaturity] : ℝ := if beforeMaturity then death else maturityDiscount

end ActuarialValuation


