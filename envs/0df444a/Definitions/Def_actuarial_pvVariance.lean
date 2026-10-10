-- Prove2me | Definitions.Def_actuarial_pvVariance
-- name    : actuarial_pvVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:07.664136+00:00
-- url     : https://prove2.me/theorems/c347b691-69fa-4fa3-821e-5a16b3feaf61
-- title:
--   Equivalence premiums and loss variance: pvVariance
-- statement:
--   Variance is the second raw moment minus squared expectation, for a fully normalised distribution.
--
--   Mathematical relation:
--
--   $$
--   pvSecondMoment p loss - (pvExpected p loss)^2
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected
import Definitions.Def_actuarial_pvSecondMoment

namespace ActuarialValuation

noncomputable def pvVariance {n : ℕ} (p loss : Fin n → ℝ) : ℝ := pvSecondMoment p loss - (pvExpected p loss)^2

end ActuarialValuation


