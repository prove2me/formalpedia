-- Prove2me | Definitions.Def_actuarial_f_post97To05IllustrativeRate
-- name    : actuarial_f_post97To05IllustrativeRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:38:44.571755+00:00
-- url     : https://prove2.me/theorems/e547b3a7-93fe-44d2-b5d0-d224dcfc99fa
-- title:
--   Illustrative LPI five per cent rate
-- statement:
--   Illustrate a zero-floored rate capped at five per cent for a potentially applicable benefit component.
--
--   The defining relationship is:
--
--   $$
--   u=\min(0.05,\max(0,\pi))
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

namespace ActuarialUnderpinsF
noncomputable def post97To05IllustrativeRate (inflation : ℝ) : ℝ :=
  lpiRate 0 (5 / 100) inflation
end ActuarialUnderpinsF


