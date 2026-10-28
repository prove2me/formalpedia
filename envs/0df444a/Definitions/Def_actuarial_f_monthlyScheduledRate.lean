-- Prove2me | Definitions.Def_actuarial_f_monthlyScheduledRate
-- name    : actuarial_f_monthlyScheduledRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:38:04.504668+00:00
-- url     : https://prove2.me/theorems/e6a74bb3-1aeb-4d4d-b3e7-9d508d2367fd
-- title:
--   First and subsequent LPI increases
-- statement:
--   Apply the capped rate times a complete-month pro-rata fraction at the first event, full capped rates at later annual events, and zero on other months.
--
--   The defining relationship is:
--
--   $$
--   u_t=\begin{cases}\alpha u_0&t=D_1\\u_k&t=D_1+12k\\0&\mathrm{otherwise}\end{cases}
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate
import Definitions.Def_actuarial_f_completeMonths
import Definitions.Def_actuarial_f_proratedAnnualRate

namespace ActuarialUnderpinsF
noncomputable def monthlyScheduledRate (retirement first : ℕ)
    (floor cap : ℝ) (inflation : ℕ → ℝ) (t : ℕ) : ℝ :=
  if retirement < first ∧ t = first then
    proratedAnnualRate (lpiRate floor cap (inflation 0))
      (completeMonths retirement first)
  else if retirement < first ∧ first < t ∧ (t - first) % 12 = 0 then
    lpiRate floor cap (inflation ((t - first) / 12))
  else 0
end ActuarialUnderpinsF


