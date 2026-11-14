-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePolynomialStep
-- name    : row23_rh_supp_RHLegendrePolynomialStep
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:03:37.890507+00:00
-- url     : https://prove2.me/theorems/044d1109-acf1-4f72-bb39-8575f021f99e
-- title:
--   Row 23 RH support: RHLegendrePolynomialStep
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRodrigues
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial MeasureTheory intervalIntegral
noncomputable def unitStep (c t : ℝ) : ℝ := if c ≤ t then 1 else 0
lemma unitStep_mono (c : ℝ) : Monotone (unitStep c) := by
  intro a b hab
  unfold unitStep
  split_ifs with ha hb
  · exact le_rfl
  · exact False.elim (hb (ha.trans hab))
  · norm_num
  · exact le_rfl
lemma polynomial_ramp_core (p : ℝ[X]) (a c : ℝ)
    (h1 : p.eval 1=0) (h1' : p.derivative.eval 1=0)
    (ha : p.eval a*(a-c)=0) (ha' : p.derivative.eval a*((a-c)^2/2)=0) :
    (∫ t : ℝ in a..1, p.derivative.derivative.eval t*((t-c)^2/2)) =
      ∫ t : ℝ in a..1, p.eval t := by
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => (u-c)^2/2) (t-c) t := by
    have h := (((hasDerivAt_id t).sub_const c).pow 2).div_const 2
    apply h.congr_deriv
    simp only [id_eq,Nat.reduceSub,pow_one,mul_one]
    ring
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t (_ : t ∈ Set.uIcc a 1) => p.hasDerivAt t)
    (fun t (_ : t ∈ Set.uIcc a 1) => (hasDerivAt_id t).sub_const c)
    (p.derivative.continuous.intervalIntegrable a 1)
    (intervalIntegrable_const (c := (1:ℝ)))
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t (_ : t ∈ Set.uIcc a 1) => p.derivative.hasDerivAt t)
    (fun t (_ : t ∈ Set.uIcc a 1) => hd t)
    (p.derivative.derivative.continuous.intervalIntegrable a 1)
    ((continuous_id.sub continuous_const).intervalIntegrable a 1)
  simp only [id_eq,mul_one,h1,zero_mul,ha,sub_self,zero_sub] at hfirst
  simp only [h1',zero_mul,ha',sub_self,zero_sub] at hsecond
  linarith
 theorem polynomial_step_second_primitive (p : ℝ[X]) (c : ℝ)
    (h0 : p.eval 0=0) (h1 : p.eval 1=0)
    (h0' : p.derivative.eval 0=0) (h1' : p.derivative.eval 1=0) :
    (∫ t : ℝ in 0..1, p.eval t*unitStep c t) =
      ∫ t : ℝ in 0..1, p.derivative.derivative.eval t*(max (t-c) 0)^2/2 := by
  have hi (a b : ℝ) : IntervalIntegrable
      (fun t : ℝ => p.derivative.derivative.eval t*(max (t-c) 0)^2/2) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hs (a b : ℝ) : IntervalIntegrable
      (fun t : ℝ => p.eval t*unitStep c t) volume a b := by
    simpa only [mul_comm] using
      ((unitStep_mono c).intervalIntegrable (a := a) (b := b)).mul_continuousOn p.continuous.continuousOn
  by_cases hc : c ≤ 0
  · have he : (∫ t : ℝ in 0..1, p.eval t*unitStep c t) = ∫ t : ℝ in 0..1, p.eval t := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      simp only [unitStep,if_pos (hc.trans ht.1),mul_one]
    have hr : (∫ t : ℝ in 0..1, p.derivative.derivative.eval t*(max (t-c) 0)^2/2) =
        ∫ t : ℝ in 0..1, p.derivative.derivative.eval t*((t-c)^2/2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      rw [max_eq_left (by linarith [ht.1] : 0 ≤ t-c)]
      ring
    rw [he,hr]
    exact (polynomial_ramp_core p 0 c h1 h1' (by rw [h0,zero_mul]) (by rw [h0',zero_mul])).symm
  have hc0 : 0 < c := lt_of_not_ge hc
  by_cases hc1 : 1 ≤ c
  · have hl : (∫ t : ℝ in 0..1, p.eval t*unitStep c t) = 0 := by
      calc
        _ = ∫ _ : ℝ in 0..1, (0:ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)
          intro t ht
          dsimp only
          simp only [unitStep,if_neg (not_le.mpr (ht.2.trans_le hc1)),mul_zero]
        _ = 0 := intervalIntegral.integral_zero
    rw [hl]
    symm
    calc
      _ = ∫ _ : ℝ in 0..1, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        rw [max_eq_right (by linarith [ht.2] : t-c ≤ 0)]
        ring
      _ = 0 := intervalIntegral.integral_zero
  have hc1' : c < 1 := lt_of_not_ge hc1
  have hl : (∫ t : ℝ in 0..c, p.eval t*unitStep c t) = 0 := by
    calc
      _ = ∫ _ : ℝ in 0..c, (0:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc0.le
        intro t ht
        dsimp only
        simp only [unitStep,if_neg (not_le.mpr ht.2),mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  have hr : (∫ t : ℝ in 0..c, p.derivative.derivative.eval t*(max (t-c) 0)^2/2) = 0 := by
    calc
      _ = ∫ _ : ℝ in 0..c, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le hc0.le] at ht
        rw [max_eq_right (by linarith [ht.2] : t-c ≤ 0)]
        ring
      _ = 0 := intervalIntegral.integral_zero
  rw [←intervalIntegral.integral_add_adjacent_intervals (hs 0 c) (hs c 1),hl,zero_add,
      ←intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c 1),hr,zero_add]
  have he : (∫ t : ℝ in c..1, p.eval t*unitStep c t) = ∫ t : ℝ in c..1, p.eval t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le hc1'.le] at ht
    simp only [unitStep,if_pos ht.1,mul_one]
  have he' : (∫ t : ℝ in c..1, p.derivative.derivative.eval t*(max (t-c) 0)^2/2) =
      ∫ t : ℝ in c..1, p.derivative.derivative.eval t*((t-c)^2/2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le hc1'.le] at ht
    rw [max_eq_left (by linarith [ht.1] : 0 ≤ t-c)]
    ring
  rw [he,he']
  exact (polynomial_ramp_core p c c h1 h1' (by simp) (by simp)).symm
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.polynomial_step_second_primitive


