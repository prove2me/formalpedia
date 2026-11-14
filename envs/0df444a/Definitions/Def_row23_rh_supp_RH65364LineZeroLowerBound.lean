-- Prove2me | Definitions.Def_row23_rh_supp_RH65364LineZeroLowerBound
-- name    : row23_rh_supp_RH65364LineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T23:04:12.904254+00:00
-- url     : https://prove2.me/theorems/f4da9295-3623-4fec-af23-6fdfbfa96b68
-- title:
--   Row 23 RH support: RH65364LineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65108LineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH65364BandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65364NewBand
theorem line_zero_lower_bound_121_65364 : RS5.BandZeros (121 : ℝ) (65364 : ℝ) 85786 := by
  have h := RH65108NewBand.line_zero_lower_bound_121_65108.glue
    (show (121 : ℝ) ≤ 65108 by norm_num) (show (65108 : ℝ) ≤ 65364 by norm_num) line_zeros
  simpa using h
end RH65364NewBand
#print axioms RH65364NewBand.line_zero_lower_bound_121_65364


