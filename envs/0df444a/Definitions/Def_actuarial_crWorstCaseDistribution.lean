-- Prove2me | Definitions.Def_actuarial_crWorstCaseDistribution
-- name    : actuarial_crWorstCaseDistribution
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:06.756988+00:00
-- url     : https://prove2.me/theorems/2f8579bb-4c2a-41a4-ac0e-cada567c3d0e
-- title:
--   Coherent worst-case actuarial premium and portfolio: crWorstCaseDistribution
-- statement:
--   One optimising distribution selected between the two candidates according to their expected monetary losses.
--
--   Mathematical relation:
--
--   $$
--   if crExpected p X ≤ crExpected q X then q i else p i
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

noncomputable def crWorstCaseDistribution {n : ℕ} (p q X : Fin n→ℝ) (i : Fin n) : ℝ := if crExpected p X ≤ crExpected q X then q i else p i

end ActuarialValuation


