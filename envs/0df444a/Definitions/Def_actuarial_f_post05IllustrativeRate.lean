-- Prove2me | Definitions.Def_actuarial_f_post05IllustrativeRate
-- name    : actuarial_f_post05IllustrativeRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:38:56.894985+00:00
-- url     : https://prove2.me/theorems/f2ef0f7a-8315-4e49-95b3-3ad9a3ee717d
-- title:
--   Illustrative LPI two-and-a-half per cent rate
-- statement:
--   Illustrate a zero-floored rate capped at two-and-a-half per cent for a potentially applicable benefit component.
--
--   The defining relationship is:
--
--   $$
--   u=\min(0.025,\max(0,\pi))
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

namespace ActuarialUnderpinsF
noncomputable def post05IllustrativeRate (inflation : ℝ) : ℝ :=
  lpiRate 0 (25 / 1000) inflation
end ActuarialUnderpinsF


