-- Prove2me | Definitions.Def_actuarial_f_gmpAdjustedReplacementEPV
-- name    : actuarial_f_gmpAdjustedReplacementEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:45:33.636984+00:00
-- url     : https://prove2.me/theorems/904b0549-6bf0-4e33-a941-94ac2277e54d
-- title:
--   Replacement liability suppressing survivor top-up on overlap
-- statement:
--   Legacy algebraic replacement comparator that suppresses the entire supplied survivor supplement on overlapping estate-guarantee dates. If that supplement contains statutory survivor GMP this comparator would not preserve the protected entitlement and MUST NOT be used as a legally certified benefit. Use the separate protected-survivor replacement definitions for the principal UK pension contract.
-- source:
--   Original derived hypothetical cashflow comparator, not a statutory survivor-payment rule. Pension Schemes Act 1993 section 17 protects survivor GMP: https://www.legislation.gov.uk/ukpga/1993/48/section/17 . This legacy variant explicitly assumes full contractual replacement and has no automatic statutory applicability.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_monthlyLinkedReplacementEPV

namespace ActuarialUnderpinsF
noncomputable def gmpAdjustedReplacementEPV
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (survivorSupplement : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  monthlyLinkedReplacementEPV n h r g p disc a b c sa sb estate
    ga gb gc gs ge +
  ∑ t ∈ Finset.range (h + 1), disc t *
    expect n h p (fun z i j =>
      memberSupplement z i t +
        if estateDue h r g i t = 1 then 0
        else survivorSupplement z i j t)
end ActuarialUnderpinsF


