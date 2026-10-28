-- Prove2me | Definitions.Def_actuarial_f_monthlyLinkedStateEPV
-- name    : actuarial_f_monthlyLinkedStateEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:40:57.457819+00:00
-- url     : https://prove2.me/theorems/c0acc95a-3684-471a-98a4-5e1d7bba8aa1
-- title:
--   Cashflow-state monthly-linked expected present value
-- statement:
--   Value the elected first tranche, separately indexed second tranche, linked survivor and estate amounts as four distinct state-conditioned streams.
--
--   The defining relationship is:
--
--   $$
--   V_S=V_1+V_2+V_S^{\ast}+V_E
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_linkedSpouseBasis
import Definitions.Def_actuarial_f_linkedFirstTranche

namespace ActuarialUnderpinsF
noncomputable def monthlyLinkedStateEPV (n h r g : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (h + 1), disc t * (
    expect n h p (fun z i j =>
      linkedFirstTranche r z i t a b ga gb) +
    gc t * expect n h p (fun z i j => c z * memberDue r i t) +
    expect n h p (fun z i j =>
      spouseInstalment h z i j t (linkedSpouseBasis a b sa sb) gs) +
    ge t * expect n h p (fun z i j =>
      estate z * estateDue h r g i t))
end ActuarialUnderpinsF


