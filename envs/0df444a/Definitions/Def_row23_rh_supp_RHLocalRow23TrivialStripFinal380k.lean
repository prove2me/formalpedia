-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalRow23TrivialStripFinal380k
-- name    : row23_rh_supp_RHLocalRow23TrivialStripFinal380k
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:48.427326+00:00
-- url     : https://prove2.me/theorems/71c6f1e7-8c6e-4277-ba2d-353c67f4bf11
-- title:
--   Row 23 RH support: RHLocalRow23TrivialStripFinal380k
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalMoment380kArithmetic
import Definitions.Def_row23_rh_supp_RHLegendreRationalRowTransfer
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
namespace DusartLegendreSmoothing.Moment380k
open RationalRows

theorem p23_trivial_strip_final :
    (p23.δ:ℝ)/2+((1+(p23.δ:ℝ)/2)*(p23.B₁:ℝ)+(p23.M:ℝ)/(p23.δ:ℝ)^p23.m*(p23.B₂:ℝ))*((p23.q:ℝ)^8)^(-1/2:ℝ)+
      ((p23.M:ℝ)/(p23.δ:ℝ)^p23.m*(p23.B₃:ℝ))*((p23.q:ℝ)^8)^((1:ℝ)-1)+2*((p23.q:ℝ)^8)^(-1:ℝ)+
      (4096/Real.pi+32*(p23.m:ℝ)/(p23.δ:ℝ))*((p23.q:ℝ)^8)^(-3/2:ℝ) ≤ (p23.ε:ℝ) := by
  have hq0 : (0:ℝ) < p23.q := by norm_num [p23]
  have hb : (p23.δ:ℝ)/2+((1+(p23.δ:ℝ)/2)*(p23.B₁:ℝ)+(p23.M:ℝ)/(p23.δ:ℝ)^p23.m*(p23.B₂:ℝ))/(p23.q:ℝ)^4+
      ((p23.M:ℝ)/(p23.δ:ℝ)^p23.m*(p23.B₃:ℝ))+2/(p23.q:ℝ)^8+
      (4096/3+32*(p23.m:ℝ)/(p23.δ:ℝ))/(p23.q:ℝ)^12 ≤ (p23.ε:ℝ) := by
    norm_num [p23]
  have h4 := eighth_power_rpow_inverse (p23.q:ℝ) hq0 4
  have h8 := eighth_power_rpow_inverse (p23.q:ℝ) hq0 8
  have h12 := eighth_power_rpow_inverse (p23.q:ℝ) hq0 12
  norm_num at h4 h8 h12
  norm_num only [show (1:ℝ)-1=0 by norm_num, Real.rpow_zero, mul_one]
  rw [h4,h8,h12]
  simp only [←div_eq_mul_inv]
  have hpi : (4096:ℝ)/Real.pi ≤ 4096/3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_three.le
  have hh := div_le_div_of_nonneg_right
    (add_le_add_right hpi (32*(p23.m:ℝ)/(p23.δ:ℝ))) (pow_nonneg hq0.le 12)
  have hh' : (4096/Real.pi+32*(p23.m:ℝ)/(p23.δ:ℝ))/(p23.q:ℝ)^12 ≤
      (4096/3+32*(p23.m:ℝ)/(p23.δ:ℝ))/(p23.q:ℝ)^12 := by
    simpa only [add_comm] using hh
  exact (add_le_add (le_refl _) hh').trans hb
end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.p23_trivial_strip_final


