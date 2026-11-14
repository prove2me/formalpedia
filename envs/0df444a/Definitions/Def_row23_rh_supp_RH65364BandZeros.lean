-- Prove2me | Definitions.Def_row23_rh_supp_RH65364BandZeros
-- name    : row23_rh_supp_RH65364BandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T23:00:39.216743+00:00
-- url     : https://prove2.me/theorems/3fc1d69d-e3b8-40c8-a036-da4b191ebe43
-- title:
--   Row 23 RH support: RH65364BandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65364BandBlock00
import Definitions.Def_row23_rh_supp_RH65364BandBlock01
import Definitions.Def_row23_rh_supp_RH65364BandBlock02
import Definitions.Def_row23_rh_supp_RH65364BandBlock03
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65364NewBand
theorem line_zeros : RS5.BandZeros (65108 : ℝ) (65364 : ℝ) 377 := by
  have h01 := RH65364BandBlock00.line_zeros.glue (show (65108 : ℝ) ≤ 65172 by norm_num) (show (65172 : ℝ) ≤ 65236 by norm_num) RH65364BandBlock01.line_zeros
  have h02 := h01.glue (show (65108 : ℝ) ≤ 65236 by norm_num) (show (65236 : ℝ) ≤ 65300 by norm_num) RH65364BandBlock02.line_zeros
  have h03 := h02.glue (show (65108 : ℝ) ≤ 65300 by norm_num) (show (65300 : ℝ) ≤ 65364 by norm_num) RH65364BandBlock03.line_zeros
  simpa using h03
end RH65364NewBand
#print axioms RH65364NewBand.line_zeros


