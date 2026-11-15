-- Prove2me | Definitions.Def_row23_rh_supp_RH66388LineZeroLowerBound
-- name    : row23_rh_supp_RH66388LineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:58:07.476203+00:00
-- url     : https://prove2.me/theorems/4fba07c9-7f76-4fc6-8f36-7c01a6a92d21
-- title:
--   Row 23 RH support: RH66388LineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Theorems.Thm_TaoFivePrimes_rh66388_count_cut_previous_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_count_cut_band_20261115
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66388NewBand

theorem line_zero_lower_bound_121_66388 : RS5.BandZeros (121 : ℝ) (66388 : ℝ) 87295 := by
  have h := TaoFivePrimes.rh66388_count_cut_previous_20261115.glue
    (show (121 : ℝ) ≤ 66132 by norm_num) (show (66132 : ℝ) ≤ 66388 by norm_num)
    TaoFivePrimes.rh66388_count_cut_band_20261115
  simpa using h
end RH66388NewBand
#print axioms RH66388NewBand.line_zero_lower_bound_121_66388


