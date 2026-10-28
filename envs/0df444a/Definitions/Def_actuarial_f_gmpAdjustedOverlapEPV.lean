-- Prove2me | Definitions.Def_actuarial_f_gmpAdjustedOverlapEPV
-- name    : actuarial_f_gmpAdjustedOverlapEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:45:45.96786+00:00
-- url     : https://prove2.me/theorems/2714c0b2-40fb-405e-beda-bcb2664d23bc
-- title:
--   Overlap includes both survivor promise and GMP top-up
-- statement:
--   Legacy algebraic difference between full parallel and full replacement comparators: all survivor instalments and the supplied survivor supplement are included in the overlap. A statutory GMP minimum may not simply be treated as a displaceable survivor supplement. The protected-overlap definition used by the root excludes statutory survivor entitlements.
-- source:
--   Original derived finite-scenario overlap identity, representing a hypothetical full replacement contract only. PSA 1993 section 17: https://www.legislation.gov.uk/ukpga/1993/48/section/17 . The GMP-safe survivor guarantee requires the separate protected variant.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_guaranteeOverlapEPV
import Definitions.Def_actuarial_f_linkedSpouseBasis

namespace ActuarialUnderpinsF
noncomputable def gmpAdjustedOverlapEPV
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ)
    (survivorSupplement : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  guaranteeOverlapEPV n h r g p disc
    (linkedSpouseBasis a b sa sb) gs +
  ∑ t ∈ Finset.range (h + 1), disc t *
    expect n h p (fun z i j =>
      if estateDue h r g i t = 1 then
        survivorSupplement z i j t else 0)
end ActuarialUnderpinsF


