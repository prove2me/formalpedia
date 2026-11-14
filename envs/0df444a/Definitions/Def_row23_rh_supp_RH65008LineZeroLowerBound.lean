-- Prove2me | Definitions.Def_row23_rh_supp_RH65008LineZeroLowerBound
-- name    : row23_rh_supp_RH65008LineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:21:03.369655+00:00
-- url     : https://prove2.me/theorems/172e7c65-7bc5-4f12-8a94-ffa338079d5d
-- title:
--   Row 23 RH support: RH65008LineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65004PriorLineBand
import Definitions.Def_row23_rh_supp_RH65000NewBandZeros
import Definitions.Def_row23_rh_supp_RH65008BandZeros
import Theorems.Thm_RS5_BandZeros_mono
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65008NewBand

theorem line_zero_lower_bound_121_65008 :
    RS5.BandZeros (121 : ℝ) (65008 : ℝ) 85262 := by
  have h0 : RS5.BandZeros (65000 : ℝ) (65004 : ℝ) 6 :=
    RH65000NewBand.six_line_zeros.mono (by norm_num) (by norm_num)
  have h1 : RS5.BandZeros (121 : ℝ) (65004 : ℝ) 85256 := by
    simpa using RH65004Count.prior_line_band.glue (by norm_num) (by norm_num) h0
  have h2 := h1.glue (show (121 : ℝ) ≤ 65004 by norm_num)
    (show (65004 : ℝ) ≤ 65008 by norm_num) six_line_zeros
  simpa using h2
end RH65008NewBand
#print axioms RH65008NewBand.line_zero_lower_bound_121_65008


