-- Prove2me | Definitions.Def_row23_rh_supp_RH67156EnhancedBandZeros
-- name    : row23_rh_supp_RH67156EnhancedBandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:47:55.743021+00:00
-- url     : https://prove2.me/theorems/16de8635-c10f-40e8-acfb-933772ec52d4
-- title:
--   Row 23 RH support: RH67156EnhancedBandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EnhancedBandBlock00
import Definitions.Def_row23_rh_supp_RH67156EnhancedBandBlock01
import Definitions.Def_row23_rh_supp_RH67156EnhancedBandBlock02
import Definitions.Def_row23_rh_supp_RH67156EnhancedBandBlock03
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace RH67156NewBand
theorem line_zeros : RS5.BandZeros (66900 : ℝ) (67156 : ℝ) 379 := by
  have h01 := RH67156EnhancedBandBlock00.line_zeros.glue (show (66900 : ℝ) ≤ 66964 by norm_num) (show (66964 : ℝ) ≤ 67028 by norm_num) RH67156EnhancedBandBlock01.line_zeros
  have h02 := h01.glue (show (66900 : ℝ) ≤ 67028 by norm_num) (show (67028 : ℝ) ≤ 67092 by norm_num) RH67156EnhancedBandBlock02.line_zeros
  have h03 := h02.glue (show (66900 : ℝ) ≤ 67092 by norm_num) (show (67092 : ℝ) ≤ 67156 by norm_num) RH67156EnhancedBandBlock03.line_zeros
  simpa using h03
end RH67156NewBand
#print axioms RH67156NewBand.line_zeros


