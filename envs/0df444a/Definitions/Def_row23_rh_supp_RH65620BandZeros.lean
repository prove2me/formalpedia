-- Prove2me | Definitions.Def_row23_rh_supp_RH65620BandZeros
-- name    : row23_rh_supp_RH65620BandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T23:03:12.739473+00:00
-- url     : https://prove2.me/theorems/6caa88e4-02b3-4fd5-8022-a020230d674e
-- title:
--   Row 23 RH support: RH65620BandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65620BandBlock00
import Definitions.Def_row23_rh_supp_RH65620BandBlock01
import Definitions.Def_row23_rh_supp_RH65620BandBlock02
import Definitions.Def_row23_rh_supp_RH65620BandBlock03
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65620NewBand
theorem line_zeros : RS5.BandZeros (65364 : ℝ) (65620 : ℝ) 377 := by
  have h01 := RH65620BandBlock00.line_zeros.glue (show (65364 : ℝ) ≤ 65428 by norm_num) (show (65428 : ℝ) ≤ 65492 by norm_num) RH65620BandBlock01.line_zeros
  have h02 := h01.glue (show (65364 : ℝ) ≤ 65492 by norm_num) (show (65492 : ℝ) ≤ 65556 by norm_num) RH65620BandBlock02.line_zeros
  have h03 := h02.glue (show (65364 : ℝ) ≤ 65556 by norm_num) (show (65556 : ℝ) ≤ 65620 by norm_num) RH65620BandBlock03.line_zeros
  simpa using h03
end RH65620NewBand
#print axioms RH65620NewBand.line_zeros


