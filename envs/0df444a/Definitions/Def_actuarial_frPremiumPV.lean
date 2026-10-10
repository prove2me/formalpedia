-- Prove2me | Definitions.Def_actuarial_frPremiumPV
-- name    : actuarial_frPremiumPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:37.835268+00:00
-- url     : https://prove2.me/theorems/285890e0-7a04-4235-9dea-37974ab309d5
-- title:
--   Fractional premiums and policy reserves: frPremiumPV
-- statement:
--   Present value of a nominal annual premium rate paid in installments, where annuityPV already includes subannual installments.
--
--   Mathematical relation:
--
--   $$
--   premium * annuityPV
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def frPremiumPV (premium annuityPV : ℝ) : ℝ := premium * annuityPV

end ActuarialValuation


