-- Prove2me | Definitions.Def_actuarial_ulShortfallPV
-- name    : actuarial_ulShortfallPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:10.387086+00:00
-- url     : https://prove2.me/theorems/09f57f58-cac8-4c91-980f-d60c65cae3f7
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulShortfallPV
-- statement:
--   Expected discounted investment guarantee liability using the scenario's actual shortfall and probability weight.
--
--   Mathematical relation:
--
--   $$
--   ∑ ω : Fin m, prob ω * discount ω * ulGuaranteeShortfall (account ω) (floor ω)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteeShortfall

namespace ActuarialValuation

noncomputable def ulShortfallPV {m : ℕ} (prob discount account floor : Fin m → ℝ) : ℝ := ∑ ω : Fin m, prob ω * discount ω * ulGuaranteeShortfall (account ω) (floor ω)

end ActuarialValuation


