-- Prove2me | Definitions.Def_actuarial_pvLoadedPremium
-- name    : actuarial_pvLoadedPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:49.22775+00:00
-- url     : https://prove2.me/theorems/2b63a63e-a2e0-4989-8ef3-3a77cc741da0
-- title:
--   Equivalence premiums and loss variance: pvLoadedPremium
-- statement:
--   The loaded annual premium is the sum of its equivalence rate and the explicit risk or expense loading.
--
--   Mathematical relation:
--
--   $$
--   equivalence + loading
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def pvLoadedPremium (equivalence loading : ℝ) : ℝ := equivalence + loading

end ActuarialValuation


