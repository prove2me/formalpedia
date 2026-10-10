-- Prove2me | Definitions.Def_actuarial_ulTypeANetRisk
-- name    : actuarial_ulTypeANetRisk
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:45.328491+00:00
-- url     : https://prove2.me/theorems/b7ec4004-da67-444e-a525-a2bb300cfe7d
-- title:
--   Type A and B mortality strain and explicit guarantee: ulTypeANetRisk
-- statement:
--   Signed Type A insurance strain before clipping: face death benefit less period-end account; economically valid when face exceeds account.
--
--   Mathematical relation:
--
--   $$
--   face-account
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulTypeANetRisk (account face : ℝ) : ℝ := face-account

end ActuarialValuation


