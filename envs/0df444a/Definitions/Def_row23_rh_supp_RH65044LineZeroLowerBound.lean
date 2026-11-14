-- Prove2me | Definitions.Def_row23_rh_supp_RH65044LineZeroLowerBound
-- name    : row23_rh_supp_RH65044LineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:26:38.047792+00:00
-- url     : https://prove2.me/theorems/c75d1110-5eac-4590-9f0e-ce1b869335cd
-- title:
--   Row 23 RH support: RH65044LineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65028LineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH65044BandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65044NewBand
theorem line_zero_lower_bound_121_65044 : RS5.BandZeros (121 : ℝ) (65044 : ℝ) 85315 := by
  have h := RH65028NewBand.line_zero_lower_bound_121_65028.glue
    (show (121 : ℝ) ≤ 65028 by norm_num) (show (65028 : ℝ) ≤ 65044 by norm_num) line_zeros
  simpa using h
end RH65044NewBand
#print axioms RH65044NewBand.line_zero_lower_bound_121_65044


