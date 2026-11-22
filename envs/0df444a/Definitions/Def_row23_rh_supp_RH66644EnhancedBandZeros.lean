-- Prove2me | Definitions.Def_row23_rh_supp_RH66644EnhancedBandZeros
-- name    : row23_rh_supp_RH66644EnhancedBandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:38:00.998998+00:00
-- url     : https://prove2.me/theorems/a5015510-2cde-460b-a6d4-9e29e23ea291
-- title:
--   Row 23 RH support: RH66644EnhancedBandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66644EnhancedBandBlock00
import Definitions.Def_row23_rh_supp_RH66644EnhancedBandBlock01
import Definitions.Def_row23_rh_supp_RH66644EnhancedBandBlock02
import Definitions.Def_row23_rh_supp_RH66644EnhancedBandBlock03
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66644NewBand
theorem line_zeros : RS5.BandZeros (66388 : ℝ) (66644 : ℝ) 378 := by
  have h01 := RH66644EnhancedBandBlock00.line_zeros.glue (show (66388 : ℝ) ≤ 66452 by norm_num) (show (66452 : ℝ) ≤ 66516 by norm_num) RH66644EnhancedBandBlock01.line_zeros
  have h02 := h01.glue (show (66388 : ℝ) ≤ 66516 by norm_num) (show (66516 : ℝ) ≤ 66580 by norm_num) RH66644EnhancedBandBlock02.line_zeros
  have h03 := h02.glue (show (66388 : ℝ) ≤ 66580 by norm_num) (show (66580 : ℝ) ≤ 66644 by norm_num) RH66644EnhancedBandBlock03.line_zeros
  simpa using h03
end RH66644NewBand
#print axioms RH66644NewBand.line_zeros


