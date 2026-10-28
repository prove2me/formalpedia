-- Prove2me | Definitions.Def_actuarial_f_monthlyLinkedReplacementEPV
-- name    : actuarial_f_monthlyLinkedReplacementEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:41:13.841184+00:00
-- url     : https://prove2.me/theorems/4f800dea-f39b-4465-a7fd-b51583edbd3a
-- title:
--   Guarantee-replacement monthly-linked value
-- statement:
--   Suppress the spouse amount only on months when an estate guarantee instalment replaces it; retain the selected member and second tranches.
--
--   The defining relationship is:
--
--   $$
--   V_R=\mathbb E[\operatorname{PV}(C^{\mathrm{rep}})]
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_replacementPayment
import Definitions.Def_actuarial_f_linkedSpouseBasis
import Definitions.Def_actuarial_f_linkedFirstTranche

namespace ActuarialUnderpinsF
noncomputable def monthlyLinkedReplacementEPV (n h r g : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) : ℝ :=
  expect n h p (fun z i j =>
    ∑ t ∈ Finset.range (h + 1), disc t *
      (linkedFirstTranche r z i t a b ga gb +
       c z * gc t * memberDue r i t +
       replacementPayment h r g z i j t
         (linkedSpouseBasis a b sa sb) gs estate ge))
end ActuarialUnderpinsF


