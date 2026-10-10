-- Prove2me | Definitions.Def_actuarial_ulCreditedRate
-- name    : actuarial_ulCreditedRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:36.637374+00:00
-- url     : https://prove2.me/theorems/a2d7f6f2-1c9b-40c7-bf2f-2606eaab25b5
-- title:
--   Monthly account premium expenses and insurance charges: ulCreditedRate
-- statement:
--   Credited interest rate clamped to contractual floor and cap with a participation fraction applied to market earnings.
--
--   Mathematical relation:
--
--   $$
--   max floor (min cap (participation*market))
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulCreditedRate (market participation floor cap : ℝ) : ℝ := max floor (min cap (participation*market))

end ActuarialValuation


