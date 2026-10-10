-- Prove2me | Definitions.Def_actuarial_pvExpected
-- name    : actuarial_pvExpected
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:36.421401+00:00
-- url     : https://prove2.me/theorems/87296b36-2fd3-43c8-96d5-66820706d7ed
-- title:
--   Equivalence premiums and loss variance: pvExpected
-- statement:
--   The expected present value is a scenario-weighted finite sum with masses that must normalise to one for distributional interpretation.
--
--   Mathematical relation:
--
--   $$
--   ∑ i : Fin n, p i * loss i
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvExpected {n : ℕ} (p loss : Fin n → ℝ) : ℝ := ∑ i : Fin n, p i * loss i

end ActuarialValuation


