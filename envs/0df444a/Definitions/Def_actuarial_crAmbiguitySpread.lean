-- Prove2me | Definitions.Def_actuarial_crAmbiguitySpread
-- name    : actuarial_crAmbiguitySpread
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:46.388206+00:00
-- url     : https://prove2.me/theorems/f37ebf96-254f-4527-9758-dfb32c4065c7
-- title:
--   Coherent worst-case actuarial premium and portfolio: crAmbiguitySpread
-- statement:
--   Positive robust premium ambiguity spread between worst and best candidate expected losses.
--
--   Mathematical relation:
--
--   $$
--   crScenarioRisk p q X-crBestCaseRisk p q X
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crBestCaseRisk

namespace ActuarialValuation

noncomputable def crAmbiguitySpread {n : ℕ} (p q X : Fin n→ℝ) : ℝ := crScenarioRisk p q X-crBestCaseRisk p q X

end ActuarialValuation


