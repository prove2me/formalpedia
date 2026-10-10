-- Prove2me | Definitions.Def_actuarial_crBestCaseRisk
-- name    : actuarial_crBestCaseRisk
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:31:16.071554+00:00
-- url     : https://prove2.me/theorems/d431d525-5820-4d31-839e-6054d5515972
-- title:
--   Coherent worst-case actuarial premium and portfolio: crBestCaseRisk
-- statement:
--   Minimum expected loss across the same pair of candidate scenario probability laws.
--
--   Mathematical relation:
--
--   $$
--   min (crExpected p X) (crExpected q X)
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

noncomputable def crBestCaseRisk {n : ℕ} (p q X : Fin n→ℝ) : ℝ := min (crExpected p X) (crExpected q X)

end ActuarialValuation


