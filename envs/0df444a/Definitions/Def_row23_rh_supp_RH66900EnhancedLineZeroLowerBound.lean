-- Prove2me | Definitions.Def_row23_rh_supp_RH66900EnhancedLineZeroLowerBound
-- name    : row23_rh_supp_RH66900EnhancedLineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:45:57.859704+00:00
-- url     : https://prove2.me/theorems/9e39c487-ddc6-407a-b406-b0f50351bf1a
-- title:
--   Row 23 RH support: RH66900EnhancedLineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66644EnhancedLineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH66900EnhancedBandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66900NewBand
theorem line_zero_lower_bound_121_66900 : RS5.BandZeros (121 : ℝ) (66900 : ℝ) 88049 := by
  have h := RH66644NewBand.line_zero_lower_bound_121_66644.glue
    (show (121 : ℝ) ≤ 66644 by norm_num) (show (66644 : ℝ) ≤ 66900 by norm_num) line_zeros
  simpa using h
end RH66900NewBand
#print axioms RH66900NewBand.line_zero_lower_bound_121_66900


