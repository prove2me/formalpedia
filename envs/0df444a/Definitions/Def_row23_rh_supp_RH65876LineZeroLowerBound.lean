-- Prove2me | Definitions.Def_row23_rh_supp_RH65876LineZeroLowerBound
-- name    : row23_rh_supp_RH65876LineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T23:12:56.317698+00:00
-- url     : https://prove2.me/theorems/11ee519f-cdf7-4110-a4f8-b4dc2fa4e2b9
-- title:
--   Row 23 RH support: RH65876LineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65620LineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH65876BandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65876NewBand
theorem line_zero_lower_bound_121_65876 : RS5.BandZeros (121 : ℝ) (65876 : ℝ) 86540 := by
  have h := RH65620NewBand.line_zero_lower_bound_121_65620.glue
    (show (121 : ℝ) ≤ 65620 by norm_num) (show (65620 : ℝ) ≤ 65876 by norm_num) line_zeros
  simpa using h
end RH65876NewBand
#print axioms RH65876NewBand.line_zero_lower_bound_121_65876


