-- Prove2me | Definitions.Def_row23_rh_supp_RH65028LineZeroLowerBound
-- name    : row23_rh_supp_RH65028LineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:24:38.990396+00:00
-- url     : https://prove2.me/theorems/1baa6dba-3607-4bb3-a342-f08ef1330a1f
-- title:
--   Row 23 RH support: RH65028LineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65012LineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH65028BandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65028NewBand
theorem line_zero_lower_bound_121_65028 : RS5.BandZeros (121 : ℝ) (65028 : ℝ) 85292 := by
  have h := RH65012NewBand.line_zero_lower_bound_121_65012.glue
    (show (121 : ℝ) ≤ 65012 by norm_num) (show (65012 : ℝ) ≤ 65028 by norm_num) line_zeros
  simpa using h
end RH65028NewBand
#print axioms RH65028NewBand.line_zero_lower_bound_121_65028


