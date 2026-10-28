-- Prove2me | Definitions.Def_actuarial_f_proratedAnnualRate
-- name    : actuarial_f_proratedAnnualRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:37:40.696832+00:00
-- url     : https://prove2.me/theorems/02a86d66-f24e-4a87-80cf-ba99ddf627b2
-- title:
--   First-increase monthly pro-rata rate
-- statement:
--   Apply a fraction of the otherwise applicable annual percentage to the first scheduled increase.
--
--   The defining relationship is:
--
--   $$
--   u_{\mathrm{first}}=u\,\frac{\min(12,m)}{12}
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def proratedAnnualRate (annual : ℝ) (months : ℕ) : ℝ :=
  annual * ((min 12 months : ℕ) : ℝ) / 12
end ActuarialUnderpinsF


