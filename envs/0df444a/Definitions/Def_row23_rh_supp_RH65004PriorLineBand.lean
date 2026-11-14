-- Prove2me | Definitions.Def_row23_rh_supp_RH65004PriorLineBand
-- name    : row23_rh_supp_RH65004PriorLineBand
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:18:14.000455+00:00
-- url     : https://prove2.me/theorems/8bb3ec53-7ee6-40cc-a1b6-a75db8ec767e
-- title:
--   Row 23 RH support: RH65004PriorLineBand
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Theorems.Thm_H65K_Platform_Low121_zeros
import Theorems.Thm_H65K_Platform_Bridge520_zeros
import Theorems.Thm_H65K_Platform_Low_zeros
import Theorems.Thm_H65K_Platform_High_zeros
import Theorems.Thm_RS5_BandZeros_mono
import Theorems.Thm_RS5_BandZeros_glue
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65004Count

/-- The earlier critical-line band assembled from the four checked source ranges. -/
theorem prior_line_band : RS5.BandZeros (121 : ℝ) (65000 : ℝ) 85250 := by
  have h0 := H65K.Platform.Low121.zeros.glue (by norm_num) (by norm_num)
    H65K.Platform.Bridge520.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K.Platform.Low.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K.Platform.High.zeros
  have h := h2.mono (show (121 : ℝ) ≤ 121 from le_rfl)
    (show (4259840000 : ℝ) / 65536 ≤ 65000 by norm_num)
  convert h using 1 <;> norm_num

end RH65004Count
#print axioms RH65004Count.prior_line_band


