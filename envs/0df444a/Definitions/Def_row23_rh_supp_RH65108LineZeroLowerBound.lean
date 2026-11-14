-- Prove2me | Definitions.Def_row23_rh_supp_RH65108LineZeroLowerBound
-- name    : row23_rh_supp_RH65108LineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T23:00:16.805387+00:00
-- url     : https://prove2.me/theorems/232a87c3-dd07-46b9-b1a8-90b3a5194a59
-- title:
--   Row 23 RH support: RH65108LineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65044LineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH65108BandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65108NewBand
theorem line_zero_lower_bound_121_65108 : RS5.BandZeros (121 : ℝ) (65108 : ℝ) 85409 := by
  have h := RH65044NewBand.line_zero_lower_bound_121_65044.glue
    (show (121 : ℝ) ≤ 65044 by norm_num) (show (65044 : ℝ) ≤ 65108 by norm_num) line_zeros
  simpa using h
end RH65108NewBand
#print axioms RH65108NewBand.line_zero_lower_bound_121_65108


