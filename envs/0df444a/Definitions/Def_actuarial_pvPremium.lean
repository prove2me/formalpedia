-- Prove2me | Definitions.Def_actuarial_pvPremium
-- name    : actuarial_pvPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:34.536691+00:00
-- url     : https://prove2.me/theorems/fda4b529-2b25-4248-a85b-fe634bceb7d4
-- title:
--   Finite random present values of insurance benefits and premium streams: pvPremium
-- statement:
--   The random present value of a premium stream is the rate times its scenario-specific premium annuity.
--
--   Mathematical relation:
--
--   $$
--   premium * annuity i
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvPremium {n : ℕ} (annuity : Fin n → ℝ) (premium : ℝ) (i : Fin n) : ℝ := premium * annuity i

end ActuarialValuation


