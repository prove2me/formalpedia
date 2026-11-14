-- Prove2me | Definitions.Def_row23_rh_supp_RH65012LineZeroLowerBound
-- name    : row23_rh_supp_RH65012LineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:22:47.364991+00:00
-- url     : https://prove2.me/theorems/951c6a8e-ffdc-41d0-9c17-65a07a89fbac
-- title:
--   Row 23 RH support: RH65012LineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65008LineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH65012BandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65012NewBand
theorem line_zero_lower_bound_121_65012 : RS5.BandZeros (121 : ℝ) (65012 : ℝ) 85268 := by
  have h := RH65008NewBand.line_zero_lower_bound_121_65008.glue
    (show (121 : ℝ) ≤ 65008 by norm_num) (show (65008 : ℝ) ≤ 65012 by norm_num) line_zeros
  simpa using h
end RH65012NewBand
#print axioms RH65012NewBand.line_zero_lower_bound_121_65012


