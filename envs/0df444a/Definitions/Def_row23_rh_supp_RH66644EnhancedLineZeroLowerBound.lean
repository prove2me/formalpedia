-- Prove2me | Definitions.Def_row23_rh_supp_RH66644EnhancedLineZeroLowerBound
-- name    : row23_rh_supp_RH66644EnhancedLineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:40:30.441336+00:00
-- url     : https://prove2.me/theorems/3ad625ac-eebd-4fcc-842e-5e939a07166f
-- title:
--   Row 23 RH support: RH66644EnhancedLineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388LineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH66644EnhancedBandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66644NewBand
theorem line_zero_lower_bound_121_66644 : RS5.BandZeros (121 : ℝ) (66644 : ℝ) 87673 := by
  have h := RH66388NewBand.line_zero_lower_bound_121_66388.glue
    (show (121 : ℝ) ≤ 66388 by norm_num) (show (66388 : ℝ) ≤ 66644 by norm_num) line_zeros
  simpa using h
end RH66644NewBand
#print axioms RH66644NewBand.line_zero_lower_bound_121_66644


