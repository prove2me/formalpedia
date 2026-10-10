-- Prove2me | Definitions.Def_actuarial_pvMass
-- name    : actuarial_pvMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:10.069548+00:00
-- url     : https://prove2.me/theorems/ae371454-7d67-4556-bb8a-0e076a98c693
-- title:
--   Actual loss distribution and percentile premium adequacy: pvMass
-- statement:
--   Discrete loss distribution assigns each realised loss value the combined probability mass of scenarios with precisely that value.
--
--   Mathematical relation:
--
--   $$
--   ∑ i : Fin n, if loss i = z then p i else 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvMass {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) : ℝ := ∑ i : Fin n, if loss i = z then p i else 0

end ActuarialValuation


