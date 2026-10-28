-- Prove2me | Definitions.Def_actuarial_f_monthlyScheduledGrowth
-- name    : actuarial_f_monthlyScheduledGrowth
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:38:18.19843+00:00
-- url     : https://prove2.me/theorems/2cca0ce0-b6c7-4026-b69a-7692441b14ff
-- title:
--   Growth from retirement without premature increases
-- statement:
--   Compound only the dated event-rate factors through the calendar month of payment. The retirement instalment has multiplier one.
--
--   The defining relationship is:
--
--   $$
--   G_t=\prod_{m=0}^{t}(1+u_m)
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledRate

namespace ActuarialUnderpinsF
noncomputable def monthlyScheduledGrowth (retirement first : ℕ)
    (floor cap : ℝ) (inflation : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∏ m ∈ Finset.range (t + 1),
    (1 + monthlyScheduledRate retirement first floor cap inflation m)
end ActuarialUnderpinsF


