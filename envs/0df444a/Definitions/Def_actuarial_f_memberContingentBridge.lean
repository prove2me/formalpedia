-- Prove2me | Definitions.Def_actuarial_f_memberContingentBridge
-- name    : actuarial_f_memberContingentBridge
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:41:23.022542+00:00
-- url     : https://prove2.me/theorems/dd74b29a-8b07-4d7d-b556-d9c669df3f4c
-- title:
--   Bridge payable while member remains entitled
-- statement:
--   Unlike an unconditional temporary cash rider, pay this bridge only in the specified date window while a member payment is due.
--
--   The defining relationship is:
--
--   $$
--   C^{\mathrm{bridge}}_t=B\,\mathbf1_{\mathrm{window}}\mathbf1_{\mathrm{member}}
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue

namespace ActuarialUnderpinsF
noncomputable def memberContingentBridge (r i start stop t : ℕ)
    (monthlyAmount : ℝ) : ℝ :=
  if start ≤ t ∧ t < stop then
    monthlyAmount * memberDue r i t else 0
end ActuarialUnderpinsF


