-- Prove2me | Definitions.Def_actuarial_f_monthlyTranchePayment
-- name    : actuarial_f_monthlyTranchePayment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:39:30.95553+00:00
-- url     : https://prove2.me/theorems/40b87daa-6cdb-46d7-929f-43fe6d36a883
-- title:
--   Many independently indexed components
-- statement:
--   Sum the date-specific payments of any finite collection of tranches and apply the member-due indicator.
--
--   The defining relationship is:
--
--   $$
--   C_t=\mathbf1_{\mathrm{due}}\sum_qB_qG_{q,t}
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue

namespace ActuarialUnderpinsF
noncomputable def monthlyTranchePayment (r z i t k : ℕ)
    (base : ℕ → ℕ → ℝ) (growth : ℕ → ℕ → ℝ) : ℝ :=
  (∑ q ∈ Finset.range k, base q z * growth q t) * memberDue r i t
end ActuarialUnderpinsF


