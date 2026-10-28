-- Prove2me | Definitions.Def_actuarial_f_monthlyIncreaseEvent
-- name    : actuarial_f_monthlyIncreaseEvent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:37:54.134602+00:00
-- url     : https://prove2.me/theorems/bb87a638-b20d-47a8-aed2-572bec193678
-- title:
--   Scheduled annual increase month
-- statement:
--   A date is a scheduled increase exactly when it is the first event or a twelve-month successor.
--
--   The defining relationship is:
--
--   $$
--   t\ge D_1,\quad(t-D_1)\bmod12=0
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def monthlyIncreaseEvent (first t : ℕ) : Prop :=
  first ≤ t ∧ (t - first) % 12 = 0
end ActuarialUnderpinsF


