-- Prove2me | Definitions.Def_actuarial_crScenarioRisk
-- name    : actuarial_crScenarioRisk
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:05.000291+00:00
-- url     : https://prove2.me/theorems/9b9fe3db-906a-4fba-a4ad-cd3d17571919
-- title:
--   Coherent worst-case actuarial premium and portfolio: crScenarioRisk
-- statement:
--   Robust actuarial loss premium requiring sufficient funds for either candidate scenario probability law, the maximum of two expected-loss functionals.
--
--   Mathematical relation:
--
--   $$
--   max (crExpected p X) (crExpected q X)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

noncomputable def crScenarioRisk {n : ℕ} (p q X : Fin n→ℝ) : ℝ := max (crExpected p X) (crExpected q X)

end ActuarialValuation


