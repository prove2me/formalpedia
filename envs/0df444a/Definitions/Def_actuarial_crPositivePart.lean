-- Prove2me | Definitions.Def_actuarial_crPositivePart
-- name    : actuarial_crPositivePart
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:29:55.878816+00:00
-- url     : https://prove2.me/theorems/a991849f-d547-4c2b-8fe7-9fec52dc94c7
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crPositivePart
-- statement:
--   Positive loss amount above zero, including equality at its boundary.
--
--   Mathematical relation:
--
--   $$
--   max x 0
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def crPositivePart (x : ℝ) : ℝ := max x 0

end ActuarialValuation


