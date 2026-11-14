-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMass8Row23_380k
-- name    : row23_rh_supp_RHLocalMass8Row23_380k
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:25:49.563473+00:00
-- url     : https://prove2.me/theorems/277ba42f-5664-49e6-8548-f4fb62579807
-- title:
--   Row 23 RH support: RHLocalMass8Row23_380k
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalMassScale
import Definitions.Def_row23_rh_supp_RHLocalMass8
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace DusartLegendreSmoothing
theorem mass8_for_row23_380k : derivativeMass 8 ((156/1000000:ℚ):ℝ) ≤ (1845000000:ℝ) := by
  have h := derivativeMass_le_scaled 8 ((1/1000000000:ℚ):ℝ)
    ((156/1000000:ℚ):ℝ) (by norm_num) (by norm_num)
  calc
    _ ≤ (1 + ((156/1000000:ℚ):ℝ))^9 * derivativeMass 8 ((1/1000000000:ℚ):ℝ) := h
    _ ≤ (1 + ((156/1000000:ℚ):ℝ))^9 * (1841000000:ℝ) :=
      mul_le_mul_of_nonneg_left RHLocalMass8.mass_bound (by positivity)
    _ ≤ (1845000000:ℝ) := by norm_num
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.mass8_for_row23_380k


