-- Prove2me | Definitions.Def_actuarial_ulGuaranteePayment
-- name    : actuarial_ulGuaranteePayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:45.410922+00:00
-- url     : https://prove2.me/theorems/6c87bf1e-6e80-4e16-862c-ccf0dffd671d
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulGuaranteePayment
-- statement:
--   Maturity or death payment equal to the greater of account balance and contractual guarantee floor.
--
--   Mathematical relation:
--
--   $$
--   max account floor
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulGuaranteePayment (account floor : ℝ) : ℝ := max account floor

end ActuarialValuation


