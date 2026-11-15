-- Prove2me | Definitions.Def_row23_rh_supp_RH66132LineZeroLowerBound
-- name    : row23_rh_supp_RH66132LineZeroLowerBound
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:39:59.970067+00:00
-- url     : https://prove2.me/theorems/af850840-8d60-4e78-bac5-a643ac15ee9f
-- title:
--   Row 23 RH support: RH66132LineZeroLowerBound
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65876LineZeroLowerBound
import Definitions.Def_row23_rh_supp_RH66132BandZeros
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66132NewBand
theorem line_zero_lower_bound_121_66132 : RS5.BandZeros (121 : ℝ) (66132 : ℝ) 86917 := by
  have h := RH65876NewBand.line_zero_lower_bound_121_65876.glue
    (show (121 : ℝ) ≤ 65876 by norm_num) (show (65876 : ℝ) ≤ 66132 by norm_num) line_zeros
  simpa using h
end RH66132NewBand
#print axioms RH66132NewBand.line_zero_lower_bound_121_66132


