-- Prove2me | Definitions.Def_actuarial_pvSecondMoment
-- name    : actuarial_pvSecondMoment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:52.086972+00:00
-- url     : https://prove2.me/theorems/0dd5d901-ccf8-4fae-ae4d-4aede54b4239
-- title:
--   Equivalence premiums and loss variance: pvSecondMoment
-- statement:
--   The expected squared insurance loss is the second raw moment of the actual finite scenario distribution.
--
--   Mathematical relation:
--
--   $$
--   ∑ i : Fin n, p i * (loss i)^2
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvSecondMoment {n : ℕ} (p loss : Fin n → ℝ) : ℝ := ∑ i : Fin n, p i * (loss i)^2

end ActuarialValuation


