-- Prove2me | Definitions.Def_actuarial_pvLoading
-- name    : actuarial_pvLoading
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:41.682978+00:00
-- url     : https://prove2.me/theorems/b437089f-41dd-4a33-8495-3cb86f92b3bf
-- title:
--   Equivalence premiums and loss variance: pvLoading
-- statement:
--   The pricing loading is the additional monetary premium rate above its equivalence-principle value.
--
--   Mathematical relation:
--
--   $$
--   charged - equivalence
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvLoading (charged equivalence : ℝ) : ℝ := charged - equivalence

end ActuarialValuation


