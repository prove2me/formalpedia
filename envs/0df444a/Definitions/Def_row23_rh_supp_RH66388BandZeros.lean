-- Prove2me | Definitions.Def_row23_rh_supp_RH66388BandZeros
-- name    : row23_rh_supp_RH66388BandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:36:57.606355+00:00
-- url     : https://prove2.me/theorems/9c306ce7-461e-4af8-ba2c-171c9c601e8f
-- title:
--   Row 23 RH support: RH66388BandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388BandBlock00
import Definitions.Def_row23_rh_supp_RH66388BandBlock01
import Definitions.Def_row23_rh_supp_RH66388BandBlock02
import Definitions.Def_row23_rh_supp_RH66388BandBlock03
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66388NewBand
theorem line_zeros : RS5.BandZeros (66132 : ℝ) (66388 : ℝ) 378 := by
  have h01 := RH66388BandBlock00.line_zeros.glue (show (66132 : ℝ) ≤ 66196 by norm_num) (show (66196 : ℝ) ≤ 66260 by norm_num) RH66388BandBlock01.line_zeros
  have h02 := h01.glue (show (66132 : ℝ) ≤ 66260 by norm_num) (show (66260 : ℝ) ≤ 66324 by norm_num) RH66388BandBlock02.line_zeros
  have h03 := h02.glue (show (66132 : ℝ) ≤ 66324 by norm_num) (show (66324 : ℝ) ≤ 66388 by norm_num) RH66388BandBlock03.line_zeros
  simpa using h03
end RH66388NewBand
#print axioms RH66388NewBand.line_zeros


