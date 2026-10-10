-- Prove2me | Definitions.Def_actuarial_pvPortfolioMean
-- name    : actuarial_pvPortfolioMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:56.907588+00:00
-- url     : https://prove2.me/theorems/227481b6-430e-4022-9455-f536c3fcb865
-- title:
--   Equivalence premiums and loss variance: pvPortfolioMean
-- statement:
--   Expected portfolio aggregate loss equals the finite sum of individual expected losses, regardless of dependence.
--
--   Mathematical relation:
--
--   $$
--   ∑ i ∈ Finset.range n, individualMean i
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvPortfolioMean (individualMean : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, individualMean i

end ActuarialValuation


