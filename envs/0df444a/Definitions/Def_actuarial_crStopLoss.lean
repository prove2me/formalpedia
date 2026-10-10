-- Prove2me | Definitions.Def_actuarial_crStopLoss
-- name    : actuarial_crStopLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:13.760156+00:00
-- url     : https://prove2.me/theorems/cb5f4d47-5a0a-4bfb-99a9-37b2518b8004
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLoss
-- statement:
--   Expected stop-loss excess loss above a monetary retention threshold d for a genuine finite loss distribution.
--
--   Mathematical relation:
--
--   $$
--   ∑ i : Fin n, p i * crPositivePart (X i-d)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crPositivePart

namespace ActuarialValuation

noncomputable def crStopLoss {n : ℕ} (p X : Fin n→ℝ) (d : ℝ) : ℝ := ∑ i : Fin n, p i * crPositivePart (X i-d)

end ActuarialValuation


