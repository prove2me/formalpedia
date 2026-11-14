-- Prove2me | Definitions.Def_row23_rh_supp_RH65876BandZeros
-- name    : row23_rh_supp_RH65876BandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T23:04:51.185204+00:00
-- url     : https://prove2.me/theorems/b17d0ae4-59be-4d1c-8942-c93738c615f6
-- title:
--   Row 23 RH support: RH65876BandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65876BandBlock00
import Definitions.Def_row23_rh_supp_RH65876BandBlock01
import Definitions.Def_row23_rh_supp_RH65876BandBlock02
import Definitions.Def_row23_rh_supp_RH65876BandBlock03
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65876NewBand
theorem line_zeros : RS5.BandZeros (65620 : ℝ) (65876 : ℝ) 377 := by
  have h01 := RH65876BandBlock00.line_zeros.glue (show (65620 : ℝ) ≤ 65684 by norm_num) (show (65684 : ℝ) ≤ 65748 by norm_num) RH65876BandBlock01.line_zeros
  have h02 := h01.glue (show (65620 : ℝ) ≤ 65748 by norm_num) (show (65748 : ℝ) ≤ 65812 by norm_num) RH65876BandBlock02.line_zeros
  have h03 := h02.glue (show (65620 : ℝ) ≤ 65812 by norm_num) (show (65812 : ℝ) ≤ 65876 by norm_num) RH65876BandBlock03.line_zeros
  simpa using h03
end RH65876NewBand
#print axioms RH65876NewBand.line_zeros


