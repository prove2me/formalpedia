-- Prove2me | Definitions.Def_actuarial_pvExpectedLoss
-- name    : actuarial_pvExpectedLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:34.663433+00:00
-- url     : https://prove2.me/theorems/e83c294f-5203-49bc-838e-3fed0166d760
-- title:
--   Equivalence premiums and loss variance: pvExpectedLoss
-- statement:
--   Expected prospective loss is the expectation over the actual scenario loss variable under the stipulated premium.
--
--   Mathematical relation:
--
--   $$
--   pvExpected p (pvLoss benefit annuity premium)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected
import Definitions.Def_actuarial_pvLoss

namespace ActuarialValuation

noncomputable def pvExpectedLoss {n : ℕ} (p benefit annuity : Fin n → ℝ) (premium : ℝ) : ℝ := pvExpected p (pvLoss benefit annuity premium)

end ActuarialValuation


