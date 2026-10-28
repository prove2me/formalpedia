-- Prove2me | Definitions.Def_actuarial_f_monthlyLinkedDirectEPV
-- name    : actuarial_f_monthlyLinkedDirectEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:40:40.554693+00:00
-- url     : https://prove2.me/theorems/8ad3424f-0bd2-4ceb-b50d-7531422448d8
-- title:
--   Direct monthly-linked expected present value
-- statement:
--   Take the expectation of the full realised monthly linked-benefit contract, preserving the finite three-way joint state law.
--
--   The defining relationship is:
--
--   $$
--   V_D=\sum_{z,i,j}p_{zij}Z_{zij}
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_monthlyLinkedRealisedPV

namespace ActuarialUnderpinsF
noncomputable def monthlyLinkedDirectEPV (n h r g : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) : ℝ :=
  expect n h p (fun z i j =>
    monthlyLinkedRealisedPV h r g z i j disc a b c
      sa sb estate ga gb gc gs ge)
end ActuarialUnderpinsF


