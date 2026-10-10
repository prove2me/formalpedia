-- Prove2me | Definitions.Def_actuarial_crExpectationMargin
-- name    : actuarial_crExpectationMargin
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:30:54.622856+00:00
-- url     : https://prove2.me/theorems/399a4c94-18bc-4e03-9ca5-d2eee5e7a2bd
-- title:
--   Actual finite loss distributions and scenario ambiguity: crExpectationMargin
-- statement:
--   Difference between expected losses under two alternative probability laws.
--
--   Mathematical relation:
--
--   $$
--   crExpected q X-crExpected p X
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

noncomputable def crExpectationMargin {n : ℕ} (p q X : Fin n→ℝ) : ℝ := crExpected q X-crExpected p X

end ActuarialValuation


