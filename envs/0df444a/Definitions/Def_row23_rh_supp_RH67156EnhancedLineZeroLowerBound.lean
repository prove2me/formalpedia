-- Prove2me | Definitions.Def_row23_rh_supp_RH67156EnhancedLineZeroLowerBound
-- name    : row23_rh_supp_RH67156EnhancedLineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:52:36.319066+00:00
-- url     : https://prove2.me/theorems/fc68dd01-ea91-4aa8-a037-65b441abab27
-- title:
--   Row 23 RH support: RH67156EnhancedLineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66900EnhancedLineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH67156EnhancedBandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH67156NewBand
theorem line_zero_lower_bound_121_67156 : RS5.BandZeros (121 : ℝ) (67156 : ℝ) 88428 := by
  have h := RH66900NewBand.line_zero_lower_bound_121_66900.glue
    (show (121 : ℝ) ≤ 66900 by norm_num) (show (66900 : ℝ) ≤ 67156 by norm_num) line_zeros
  simpa using h
end RH67156NewBand
#print axioms RH67156NewBand.line_zero_lower_bound_121_67156


