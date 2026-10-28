-- Prove2me | Definitions.Def_actuarial_f_monthlyLinkedRealisedPV
-- name    : actuarial_f_monthlyLinkedRealisedPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:40:17.363049+00:00
-- url     : https://prove2.me/theorems/4324c420-8503-4fba-a221-4c6a5577d5a9
-- title:
--   Realised monthly-contract present value
-- statement:
--   Discount and sum every instalment on a finite monthly timeline for a fixed joint award-and-mortality scenario.
--
--   The defining relationship is:
--
--   $$
--   Z_{zij}=\sum_tv_t C_t(z,i,j)
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyLinkedInstalment

namespace ActuarialUnderpinsF
noncomputable def monthlyLinkedRealisedPV (h r g z i j : ℕ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (h + 1), disc t *
    monthlyLinkedInstalment h r g z i j t
      a b c sa sb estate ga gb gc gs ge
end ActuarialUnderpinsF


