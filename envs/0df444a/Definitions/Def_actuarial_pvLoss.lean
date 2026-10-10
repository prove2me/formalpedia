-- Prove2me | Definitions.Def_actuarial_pvLoss
-- name    : actuarial_pvLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:46.105973+00:00
-- url     : https://prove2.me/theorems/49b79dda-d4e0-4f32-8c1e-c56052048b46
-- title:
--   Finite random present values of insurance benefits and premium streams: pvLoss
-- statement:
--   Prospective random loss is benefit present value less premiums received, both evaluated on the same realised lifetime scenario.
--
--   Mathematical relation:
--
--   $$
--   benefit i - pvPremium annuity premium i
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvPremium

namespace ActuarialValuation

noncomputable def pvLoss {n : ℕ} (benefit annuity : Fin n → ℝ) (premium : ℝ) (i : Fin n) : ℝ := benefit i - pvPremium annuity premium i

end ActuarialValuation


