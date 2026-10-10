-- Prove2me | Definitions.Def_actuarial_ulGuaranteeShortfall
-- name    : actuarial_ulGuaranteeShortfall
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:50.728902+00:00
-- url     : https://prove2.me/theorems/dd950045-70b0-4f49-8aab-ea65fc5bfb52
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulGuaranteeShortfall
-- statement:
--   Option-like additional insurer cashflow above the policyholder's own account when the guarantee binds.
--
--   Mathematical relation:
--
--   $$
--   max (floor-account) 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulGuaranteeShortfall (account floor : ℝ) : ℝ := max (floor-account) 0

end ActuarialValuation


