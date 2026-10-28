-- Prove2me | Definitions.Def_actuarial_f_monthlyLinkedInstalment
-- name    : actuarial_f_monthlyLinkedInstalment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:39:54.834195+00:00
-- url     : https://prove2.me/theorems/06d5248b-b1f0-4110-ad6f-ae1c79ddc1ea
-- title:
--   Calendar-specific linked member survivor and estate cashflow
-- statement:
--   Add the selected first tranche, an independently indexed second tranche, the survivor pension linked to the elected option and the specified estate benefit.
--
--   The defining relationship is:
--
--   $$
--   C_t=C^{(1)}_t+C^{(2)}_t+C^S_t+C^E_t
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_linkedSpouseBasis
import Definitions.Def_actuarial_f_linkedFirstTranche

namespace ActuarialUnderpinsF
noncomputable def monthlyLinkedInstalment (h r g z i j t : ℕ)
    (a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate : ℕ → ℝ) (ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) : ℝ :=
  linkedFirstTranche r z i t a b ga gb +
    c z * gc t * memberDue r i t +
    spouseInstalment h z i j t (linkedSpouseBasis a b sa sb) gs +
    estateInstalment h r g z i t estate ge
end ActuarialUnderpinsF


