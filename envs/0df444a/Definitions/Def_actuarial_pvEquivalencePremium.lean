-- Prove2me | Definitions.Def_actuarial_pvEquivalencePremium
-- name    : actuarial_pvEquivalencePremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:19.77727+00:00
-- url     : https://prove2.me/theorems/f1e1f734-9431-4b0e-aae1-6bc5fd415971
-- title:
--   Equivalence premiums and loss variance: pvEquivalencePremium
-- statement:
--   The equivalence-premium rate balances expected random benefit PV and expected premium annuity PV when the denominator is nonzero.
--
--   Mathematical relation:
--
--   $$
--   pvExpected p benefit / pvExpected p annuity
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

noncomputable def pvEquivalencePremium {n : ℕ} (p benefit annuity : Fin n → ℝ) : ℝ := pvExpected p benefit / pvExpected p annuity

end ActuarialValuation


