-- Prove2me | Definitions.Def_actuarial_f_periodicMemberDue
-- name    : actuarial_f_periodicMemberDue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:39:39.095855+00:00
-- url     : https://prove2.me/theorems/6238de7a-07f9-431a-afe1-66c695d865ac
-- title:
--   Member instalments at a specified frequency
-- statement:
--   Require a positive payment frequency in months and that the due month lies on the retirement-based payment grid while the member is entitled.
--
--   The defining relationship is:
--
--   $$
--   t-R\equiv0\pmod f
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialUnderpinsF
noncomputable def periodicMemberDue (r i t frequencyMonths : ℕ) : ℝ :=
  if 0 < frequencyMonths ∧ r ≤ t ∧ t ≤ i ∧
      (t - r) % frequencyMonths = 0 then 1 else 0
end ActuarialUnderpinsF


