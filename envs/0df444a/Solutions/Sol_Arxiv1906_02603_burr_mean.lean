-- Prove2me | solution 1 for Arxiv1906_02603.burr_mean
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T06:21:56.48786+00:00
-- url     : https://prove2.me/submissions/a29e0e98-91ea-4a1b-87e1-38983bebfea9

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Set

namespace S80Beta

lemma beta01 (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ (c - 1) =
      Real.Gamma a * Real.Gamma c / Real.Gamma (a + c) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (c : ℂ) (by simpa using ha) (by simpa using hc)
  unfold Complex.betaIntegral at h
  have h2 : (∫ x in (0:ℝ)..1, (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((c : ℂ) - 1)) =
      ∫ x in (0:ℝ)..1, ((x ^ (a - 1) * (1 - x) ^ (c - 1) : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    simp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (by linarith [hx.2])]
    push_cast; ring_nf
  rw [h2, intervalIntegral.integral_ofReal, ← Complex.ofReal_add, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  exact_mod_cast h

lemma img : (fun t : ℝ => t / (1 + t)) '' Ioi 0 = Ioo 0 1 := by
  ext y; simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by linarith)]; linarith
  · rintro ⟨h0, h1⟩
    refine ⟨y / (1 - y), div_pos h0 (by linarith), ?_⟩
    have : 1 - y ≠ 0 := by linarith
    field_simp; ring

lemma betaIoi (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∫ t in Ioi (0:ℝ), t ^ (a - 1) * (1 + t) ^ (-(a + c)) =
      Real.Gamma a * Real.Gamma c / Real.Gamma (a + c) := by
  rw [← beta01 a c ha hc, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, ← img]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (f' := fun t => 1 / (1 + t) ^ 2)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [mem_Ioi] at ht
    have h1 : 0 < 1 + t := by linarith
    simp only [smul_eq_mul]
    rw [abs_of_pos (by positivity)]
    have e1 : 1 - t / (1 + t) = (1 + t)⁻¹ := by field_simp; ring
    rw [e1, Real.div_rpow ht.le h1.le, Real.inv_rpow h1.le]
    rw [show -(a + c) = -(a - 1) - (c - 1) - 2 by ring, Real.rpow_sub h1, Real.rpow_sub h1,
      Real.rpow_neg h1.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  · intro t ht
    simp only [mem_Ioi] at ht
    have h1 : 1 + t ≠ 0 := by linarith
    have := ((hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) h1)
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp
  · intro t ht u hu htu
    simp only [mem_Ioi] at ht hu
    have h1 : 1 + t ≠ 0 := by linarith
    have h2 : 1 + u ≠ 0 := by linarith
    simp only at htu
    field_simp at htu
    linarith

lemma f_deriv : ∀ t ∈ Ioi (0:ℝ), HasDerivWithinAt (fun t : ℝ => t / (1 + t)) (1 / (1 + t) ^ 2) (Ioi 0) t := by
  intro t ht
  simp only [mem_Ioi] at ht
  have h1 : 1 + t ≠ 0 := by linarith
  have := ((hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) h1)
  refine (this.congr_deriv ?_).hasDerivWithinAt
  simp

lemma f_inj : InjOn (fun t : ℝ => t / (1 + t)) (Ioi 0) := by
  intro t ht u hu htu
  simp only [mem_Ioi] at ht hu
  have h1 : 1 + t ≠ 0 := by linarith
  have h2 : 1 + u ≠ 0 := by linarith
  simp only at htu
  field_simp at htu
  linarith

lemma betaIoi_int (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (1 + t) ^ (-(a + c))) (Ioi 0) := by
  have hc' := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (c : ℂ)) (by simpa using ha)
    (by simpa using hc)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hc'
  have hre := hc'.re
  have hr : IntegrableOn (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (c - 1)) (Ioo 0 1) := by
    refine IntegrableOn.congr_fun (μ := volume) hre (fun x hx => ?_) measurableSet_Ioo
    simp only [mem_Ioo] at hx
    have e : ((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((c : ℂ) - 1)) =
        ((x ^ (a - 1) * (1 - x) ^ (c - 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (by linarith [hx.2])]
      push_cast; ring_nf
    simp only [e]
    rfl
  rw [← img, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi f_deriv f_inj] at hr
  refine hr.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [mem_Ioi] at ht
  have h1 : 0 < 1 + t := by linarith
  simp only [smul_eq_mul]
  symm
  rw [abs_of_pos (by positivity)]
  have e1 : 1 - t / (1 + t) = (1 + t)⁻¹ := by field_simp; ring
  rw [e1, Real.div_rpow ht.le h1.le, Real.inv_rpow h1.le]
  rw [show -(a + c) = -(a - 1) - (c - 1) - 2 by ring, Real.rpow_sub h1, Real.rpow_sub h1,
    Real.rpow_neg h1.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  field_simp

lemma img2 (lam : ℝ) (hlam : 0 < lam) : (fun t : ℝ => lam * Real.sqrt t) '' Ioi 0 = Ioi 0 := by
  ext y; simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨t, ht, rfl⟩; have := Real.sqrt_pos.2 ht; positivity
  · intro hy
    refine ⟨(y / lam) ^ 2, by positivity, ?_⟩
    rw [Real.sqrt_sq (by positivity)]; field_simp

lemma g_deriv (lam : ℝ) : ∀ t ∈ Ioi (0:ℝ),
    HasDerivWithinAt (fun t : ℝ => lam * Real.sqrt t) (lam * (1 / (2 * Real.sqrt t))) (Ioi 0) t := by
  intro t ht
  exact ((Real.hasDerivAt_sqrt (ne_of_gt ht)).const_mul lam).hasDerivWithinAt

lemma g_inj (lam : ℝ) (hlam : 0 < lam) : InjOn (fun t : ℝ => lam * Real.sqrt t) (Ioi 0) := by
  intro t ht u hu h
  simp only [mem_Ioi] at ht hu
  have h2 : Real.sqrt t = Real.sqrt u := by
    have := mul_left_cancel₀ hlam.ne' h; exact this
  have := congrArg (· ^ 2) h2
  simp only [Real.sq_sqrt ht.le, Real.sq_sqrt hu.le] at this
  exact this

end S80Beta

open Arxiv1906_02603 S80Beta in
theorem solution (lam b : ℝ) (hlam : 0 < lam) (hb : 3 / 2 < b) :
    IntegrableOn (fun A : ℝ => A ^ 1 * burrPdf lam b A) (Ioi 0) ∧
    burrMoment lam b 1 =
      lam * (-1 + b) * Real.sqrt Real.pi * Real.Gamma (-3 / 2 + b) / (2 * Real.Gamma b) := by
  have key : ∀ t ∈ Ioi (0:ℝ), |lam * (1 / (2 * Real.sqrt t))| •
      ((lam * Real.sqrt t) ^ 1 * burrPdf lam b (lam * Real.sqrt t)) =
      lam * (b - 1) * (t ^ ((3 / 2 : ℝ) - 1) * (1 + t) ^ (-((3 / 2 : ℝ) + (b - 3 / 2)))) := by
    intro t ht
    simp only [mem_Ioi] at ht
    have hs := Real.sqrt_pos.2 ht
    have h1 : 0 < 1 + t := by linarith
    rw [abs_of_pos (by positivity), smul_eq_mul, pow_one]
    unfold burrPdf
    rw [show lam * Real.sqrt t / lam = Real.sqrt t by field_simp, Real.sq_sqrt ht.le,
      show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, show -((3 / 2 : ℝ) + (b - 3 / 2)) = -b by ring,
      Real.rpow_neg h1.le, ← Real.sqrt_eq_rpow, add_comm t 1]
    have hb' : 0 < (1 + t) ^ b := Real.rpow_pos_of_pos h1 b
    field_simp
  have hint := (betaIoi_int (3 / 2) (b - 3 / 2) (by norm_num) (by linarith)).const_mul (lam * (b - 1))
  refine ⟨?_, ?_⟩
  · rw [← img2 lam hlam, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (g_deriv lam) (g_inj lam hlam)]
    exact IntegrableOn.congr_fun (μ := volume) hint (fun t ht => (key t ht).symm) measurableSet_Ioi
  · unfold burrMoment
    rw [← img2 lam hlam, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (g_deriv lam) (g_inj lam hlam), setIntegral_congr_fun measurableSet_Ioi key,
      integral_const_mul, betaIoi _ _ (by norm_num) (by linarith)]
    have hG : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
        Real.Gamma_one_half_eq]; ring
    rw [hG, show (3 / 2 : ℝ) + (b - 3 / 2) = b by ring, show (-3 / 2 + b) = b - 3 / 2 by ring]
    ring

