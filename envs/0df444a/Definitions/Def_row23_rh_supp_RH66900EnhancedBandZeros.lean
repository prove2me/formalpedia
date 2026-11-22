-- Prove2me | Definitions.Def_row23_rh_supp_RH66900EnhancedBandZeros
-- name    : row23_rh_supp_RH66900EnhancedBandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:41:26.405189+00:00
-- url     : https://prove2.me/theorems/c3afd30e-a255-486d-88cc-384d793eff0b
-- title:
--   Row 23 RH support: RH66900EnhancedBandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66900EnhancedBandBlock00
import Definitions.Def_row23_rh_supp_RH66900EnhancedBandBlock01
import Definitions.Def_row23_rh_supp_RH66900EnhancedBandBlock02
import Definitions.Def_row23_rh_supp_RH66900EnhancedBandBlock03
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66900NewBand
theorem line_zeros : RS5.BandZeros (66644 : ℝ) (66900 : ℝ) 376 := by
  have h01 := RH66900EnhancedBandBlock00.line_zeros.glue (show (66644 : ℝ) ≤ 66708 by norm_num) (show (66708 : ℝ) ≤ 66772 by norm_num) RH66900EnhancedBandBlock01.line_zeros
  have h02 := h01.glue (show (66644 : ℝ) ≤ 66772 by norm_num) (show (66772 : ℝ) ≤ 66836 by norm_num) RH66900EnhancedBandBlock02.line_zeros
  have h03 := h02.glue (show (66644 : ℝ) ≤ 66836 by norm_num) (show (66836 : ℝ) ≤ 66900 by norm_num) RH66900EnhancedBandBlock03.line_zeros
  simpa using h03
end RH66900NewBand
#print axioms RH66900NewBand.line_zeros


