-- Prove2me | Definitions.Def_actuarial_frNetPremium
-- name    : actuarial_frNetPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:14:30.406388+00:00
-- url     : https://prove2.me/theorems/fb52f64f-f1b6-4246-9691-cb155629db8e
-- title:
--   Fractional premiums and policy reserves: frNetPremium
-- statement:
--   The equivalence-principle premium rate divides expected discounted benefit cost by discounted unit-premium annuity value; positive annuity is required economically.
--
--   Mathematical relation:
--
--   $$
--   benefitPV / annuityPV
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def frNetPremium (benefitPV annuityPV : ℝ) : ℝ := benefitPV / annuityPV

end ActuarialValuation


