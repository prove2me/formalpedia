-- Prove2me | Definitions.Def_actuarial_ulAccountPV
-- name    : actuarial_ulAccountPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:58.988983+00:00
-- url     : https://prove2.me/theorems/53b64e1e-d170-48cf-a1c2-4e14820e0fa5
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulAccountPV
-- statement:
--   Expected discounted random policy account at claim time using genuine finite-scenario state probabilities.
--
--   Mathematical relation:
--
--   $$
--   ∑ ω : Fin m, prob ω * discount ω * account ω
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulAccountPV {m : ℕ} (prob discount account : Fin m → ℝ) : ℝ := ∑ ω : Fin m, prob ω * discount ω * account ω

end ActuarialValuation


