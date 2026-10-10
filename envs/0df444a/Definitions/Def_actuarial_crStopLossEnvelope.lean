-- Prove2me | Definitions.Def_actuarial_crStopLossEnvelope
-- name    : actuarial_crStopLossEnvelope
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:30.631036+00:00
-- url     : https://prove2.me/theorems/9b738f24-4e9e-4526-9ecb-933f81517816
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLossEnvelope
-- statement:
--   Worst-case expected excess-of-loss claim between two plausible probability scenarios at the same deductible.
--
--   Mathematical relation:
--
--   $$
--   max (crStopLoss p X d) (crStopLoss q X d)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLoss

namespace ActuarialValuation

noncomputable def crStopLossEnvelope {n : ℕ} (p q X : Fin n→ℝ) (d : ℝ) : ℝ := max (crStopLoss p X d) (crStopLoss q X d)

end ActuarialValuation


