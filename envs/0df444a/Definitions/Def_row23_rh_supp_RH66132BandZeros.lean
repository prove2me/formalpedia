-- Prove2me | Definitions.Def_row23_rh_supp_RH66132BandZeros
-- name    : row23_rh_supp_RH66132BandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T23:07:35.249418+00:00
-- url     : https://prove2.me/theorems/d07fd240-bfb3-41ff-b14e-9728a756d745
-- title:
--   Row 23 RH support: RH66132BandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66132BandBlock00
import Definitions.Def_row23_rh_supp_RH66132BandBlock01
import Definitions.Def_row23_rh_supp_RH66132BandBlock02
import Definitions.Def_row23_rh_supp_RH66132BandBlock03
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66132NewBand
theorem line_zeros : RS5.BandZeros (65876 : ℝ) (66132 : ℝ) 377 := by
  have h01 := RH66132BandBlock00.line_zeros.glue (show (65876 : ℝ) ≤ 65940 by norm_num) (show (65940 : ℝ) ≤ 66004 by norm_num) RH66132BandBlock01.line_zeros
  have h02 := h01.glue (show (65876 : ℝ) ≤ 66004 by norm_num) (show (66004 : ℝ) ≤ 66068 by norm_num) RH66132BandBlock02.line_zeros
  have h03 := h02.glue (show (65876 : ℝ) ≤ 66068 by norm_num) (show (66068 : ℝ) ≤ 66132 by norm_num) RH66132BandBlock03.line_zeros
  simpa using h03
end RH66132NewBand
#print axioms RH66132NewBand.line_zeros


