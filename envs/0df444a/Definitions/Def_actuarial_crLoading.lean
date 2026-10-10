-- Prove2me | Definitions.Def_actuarial_crLoading
-- name    : actuarial_crLoading
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:23.614387+00:00
-- url     : https://prove2.me/theorems/8da1560a-ee02-480f-b0eb-283f404d825f
-- title:
--   Coherent worst-case actuarial premium and portfolio: crLoading
-- statement:
--   Nonnegative robust risk loading above the first probability law's equivalence premium.
--
--   Mathematical relation:
--
--   $$
--   crScenarioRisk p q X-crExpected p X
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

noncomputable def crLoading {n : ℕ} (p q X : Fin n→ℝ) : ℝ := crScenarioRisk p q X-crExpected p X

end ActuarialValuation


