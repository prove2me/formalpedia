-- Prove2me | Definitions.Def_actuarial_f_gmpProtectedSurvivorMinimum
-- name    : actuarial_f_gmpProtectedSurvivorMinimum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:47:00.819987+00:00
-- url     : https://prove2.me/theorems/e035a8ed-c5b8-4fad-95a5-62c1dbbb14ab
-- title:
--   Eligible survivor GMP minimum per instalment
-- statement:
--   Illustrative surrogate for eligible survivor GMP at a later monthly instalment: for a surviving eligible beneficiary, the pre-88 amount plus post-88 amount increased using 6 April factors from the date of the immediately following instalment. The formula multiplies by the survivor-due indicator and floors at zero. Its commencement convention is expressly NOT a general statutory rule. The integrated capstone instead uses an independently certified survivor GMP payable date and never assumes death and commencement coincide.
-- source:
--   Illustrative finite-date model only. Pension Schemes Act 1993 sections 17 and 109 govern survivor entitlement and increase requirements: https://www.legislation.gov.uk/ukpga/1993/48/section/17 ; https://www.legislation.gov.uk/ukpga/1993/48/section/109 . The next-instalment commencement convention is a simplifying mathematical assumption, not a statement of UK statutory eligibility.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_gmpBoundedPost88Growth

namespace ActuarialUnderpinsF
noncomputable def gmpProtectedSurvivorMinimum
    (h z i j t : ℕ) (dateOf : ℕ → ℕ)
    (qualifies : ℕ → ℕ → Bool)
    (pre88 post88 : ℕ → ℕ → ℝ)
    (annualOrder : ℕ → ℝ) : ℝ :=
  (max 0 (if qualifies z i then
    pre88 z i + post88 z i *
      gmpBoundedPost88Growth (dateOf (i+1)) (dateOf t) annualOrder
   else 0)) * spouseDue h i j t
end ActuarialUnderpinsF


