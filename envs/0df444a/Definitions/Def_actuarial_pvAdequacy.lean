-- Prove2me | Definitions.Def_actuarial_pvAdequacy
-- name    : actuarial_pvAdequacy
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:28.53495+00:00
-- url     : https://prove2.me/theorems/d553851b-6b54-4523-a3ca-47e7982db7d7
-- title:
--   Actual loss distribution and percentile premium adequacy: pvAdequacy
-- statement:
--   Premium adequacy probability is the exact mass of scenarios where premium receipts cover insurance benefits.
--
--   Mathematical relation:
--
--   $$
--   ∑ i : Fin n, if benefit i ≤ premium * annuity i then p i else 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvAdequacy {n : ℕ} (p benefit annuity : Fin n → ℝ) (premium : ℝ) : ℝ := ∑ i : Fin n, if benefit i ≤ premium * annuity i then p i else 0

end ActuarialValuation


