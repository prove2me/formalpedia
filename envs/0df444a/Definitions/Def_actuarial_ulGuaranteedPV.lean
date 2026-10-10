-- Prove2me | Definitions.Def_actuarial_ulGuaranteedPV
-- name    : actuarial_ulGuaranteedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:22.460979+00:00
-- url     : https://prove2.me/theorems/09649a27-4398-4da6-ab5a-e0c3526d0153
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulGuaranteedPV
-- statement:
--   Expected discounted total policy benefit consisting of the existing account plus insurer guarantee shortfall.
--
--   Mathematical relation:
--
--   $$
--   ∑ ω : Fin m, prob ω * discount ω * ulGuaranteePayment (account ω) (floor ω)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteePayment

namespace ActuarialValuation

noncomputable def ulGuaranteedPV {m : ℕ} (prob discount account floor : Fin m → ℝ) : ℝ := ∑ ω : Fin m, prob ω * discount ω * ulGuaranteePayment (account ω) (floor ω)

end ActuarialValuation


