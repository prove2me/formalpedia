-- Prove2me | solution 1 for Arxiv1906_02603.burr_snr
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T06:25:30.596466+00:00
-- url     : https://prove2.me/submissions/eddf58ec-85c8-4c77-b6c4-046cd18d2ebb

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


open Arxiv1906_02603 in
lemma moment (lam b : ℝ) (hlam : 0 < lam) (n : ℕ) (hc : ((n:ℝ) + 2) / 2 < b) :
    IntegrableOn (fun A : ℝ => A ^ n * burrPdf lam b A) (Ioi 0) ∧
    ∫ A in Ioi (0:ℝ), A ^ n * burrPdf lam b A = lam ^ n * (b - 1) *
      (Real.Gamma (((n:ℝ) + 2) / 2) * Real.Gamma (b - ((n:ℝ) + 2) / 2) / Real.Gamma b) := by
  set a : ℝ := ((n:ℝ) + 2) / 2 with ha
  have key : ∀ t ∈ Ioi (0:ℝ), |lam * (1 / (2 * Real.sqrt t))| •
      ((lam * Real.sqrt t) ^ n * burrPdf lam b (lam * Real.sqrt t)) =
      lam ^ n * (b - 1) * (t ^ (a - 1) * (1 + t) ^ (-(a + (b - a)))) := by
    intro t ht
    simp only [mem_Ioi] at ht
    have hs := Real.sqrt_pos.2 ht
    have h1 : 0 < 1 + t := by linarith
    rw [abs_of_pos (by positivity), smul_eq_mul]
    unfold burrPdf
    have hpow : Real.sqrt t ^ n = t ^ ((n:ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]; ring_nf
    have ha1 : t ^ (a - 1) = t ^ ((n:ℝ) / 2) := by rw [ha]; ring_nf
    rw [show lam * Real.sqrt t / lam = Real.sqrt t by field_simp, Real.sq_sqrt ht.le,
      show -(a + (b - a)) = -b by ring, Real.rpow_neg h1.le, ha1, mul_pow, hpow, add_comm t 1]
    have hb' : 0 < (1 + t) ^ b := Real.rpow_pos_of_pos h1 b
    field_simp
  have hint := (betaIoi_int a (b - a) (by rw [ha]; positivity) (by linarith)).const_mul (lam ^ n * (b - 1))
  refine ⟨?_, ?_⟩
  · rw [← img2 lam hlam, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (g_deriv lam) (g_inj lam hlam)]
    exact IntegrableOn.congr_fun (μ := volume) hint (fun t ht => (key t ht).symm) measurableSet_Ioi
  · rw [← img2 lam hlam, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (g_deriv lam) (g_inj lam hlam), setIntegral_congr_fun measurableSet_Ioi key,
      integral_const_mul, betaIoi _ _ (by rw [ha]; positivity) (by linarith)]
    rw [show a + (b - a) = b by ring]

end S80Beta

open Arxiv1906_02603 S80Beta in
theorem solution (lam b : ℝ) (hlam : 0 < lam) (hb : 2 < b) :
    0 < burrMoment lam b 2 - burrMoment lam b 1 ^ 2 ∧
    burrSNR lam b = Real.Gamma (-3 / 2 + b) /
      Real.sqrt (4 * (b - 2) * Real.Gamma (b - 2) ^ 2 / Real.pi - Real.Gamma (-3 / 2 + b) ^ 2) := by
  obtain ⟨i0, m0⟩ := moment lam b hlam 0 (by norm_num; linarith)
  obtain ⟨i1, m1⟩ := moment lam b hlam 1 (by norm_num; linarith)
  obtain ⟨i2, m2⟩ := moment lam b hlam 2 (by norm_num; linarith)
  norm_num at m0 m1 m2
  have hG3 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]; ring
  have gb1 : Real.Gamma b = (b - 1) * Real.Gamma (b - 1) := by
    rw [← Real.Gamma_add_one (by linarith)]; ring_nf
  have gb2 : Real.Gamma (b - 1) = (b - 2) * Real.Gamma (b - 2) := by
    rw [← Real.Gamma_add_one (by linarith)]; ring_nf
  have hGpos : 0 < Real.Gamma (b - 2) := Real.Gamma_pos_of_pos (by linarith)
  have hb2 : 0 < b - 2 := by linarith
  have hb1 : b - 1 ≠ 0 := by linarith
  set G := Real.Gamma (b - 2)
  set H := Real.Gamma (b - 3 / 2)
  have hP : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hPpos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have M0 : ∫ A in Ioi (0:ℝ), A ^ 0 * burrPdf lam b A = 1 := by
    simp only [pow_zero, one_mul]; rw [m0, gb1]
    have := Real.Gamma_pos_of_pos (show 0 < b - 1 by linarith)
    field_simp
  have M1 : burrMoment lam b 1 = lam * Real.sqrt Real.pi * H / (2 * (b - 2) * G) := by
    unfold burrMoment; simp only [pow_one]; rw [m1, hG3, gb1, gb2]; field_simp
  have M2 : burrMoment lam b 2 = lam ^ 2 / (b - 2) := by
    unfold burrMoment; rw [m2, gb1, gb2]; field_simp
  have hvar : ∫ A in Ioi (0:ℝ), (A - (burrMoment lam b 1)) ^ 2 * burrPdf lam b A =
      burrMoment lam b 2 - (burrMoment lam b 1) ^ 2 := by
    have e : ∀ A : ℝ, (A - (burrMoment lam b 1)) ^ 2 * burrPdf lam b A = A ^ 2 * burrPdf lam b A -
        (2 * (burrMoment lam b 1)) * (A ^ 1 * burrPdf lam b A) + (burrMoment lam b 1) ^ 2 * (A ^ 0 * burrPdf lam b A) := by
      intro A; ring
    simp_rw [e]
    have j1 := i2.sub (i1.const_mul (2 * (burrMoment lam b 1)))
    have j2 := i0.const_mul (burrMoment lam b 1 ^ 2)
    rw [integral_add (μ := volume.restrict (Ioi 0))
      (f := fun A => A ^ 2 * burrPdf lam b A - 2 * (burrMoment lam b 1) * (A ^ 1 * burrPdf lam b A))
      (g := fun A => (burrMoment lam b 1) ^ 2 * (A ^ 0 * burrPdf lam b A)) (by exact j1) (by exact j2)]
    rw [integral_sub (μ := volume.restrict (Ioi 0)) (f := fun A => A ^ 2 * burrPdf lam b A)
      (g := fun A => 2 * (burrMoment lam b 1) * (A ^ 1 * burrPdf lam b A)) (by exact i2) (by exact i1.const_mul (2 * (burrMoment lam b 1))),
      integral_const_mul, integral_const_mul, M0]
    unfold burrMoment
    ring
  have hpos : 0 < burrMoment lam b 2 - (burrMoment lam b 1) ^ 2 := by
    rw [← hvar]
    have hint : IntegrableOn (fun A : ℝ => (A - (burrMoment lam b 1)) ^ 2 * burrPdf lam b A) (Ioi 0) := by
      have := (i2.sub (i1.const_mul (2 * (burrMoment lam b 1)))).add (i0.const_mul (burrMoment lam b 1 ^ 2))
      refine IntegrableOn.congr_fun (μ := volume) this (fun A _ => by simp only [Pi.add_apply, Pi.sub_apply]; ring) measurableSet_Ioi
    have hpdf : ∀ A : ℝ, 0 < A → 0 < burrPdf lam b A := by
      intro A hA; unfold burrPdf
      have : 0 < ((A / lam) ^ 2 + 1) ^ b := Real.rpow_pos_of_pos (by positivity) b
      have : 0 < b - 1 := by linarith
      positivity
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
    · have hsub : Ioo (|(burrMoment lam b 1)| + 1) (|(burrMoment lam b 1)| + 2) ⊆ Function.support (fun A : ℝ => (A - (burrMoment lam b 1)) ^ 2 * burrPdf lam b A) ∩ Ioi 0 := by
        intro A hA
        simp only [mem_Ioo] at hA
        have hA0 : 0 < A := by linarith [abs_nonneg (burrMoment lam b 1)]
        have hAm : A - (burrMoment lam b 1) ≠ 0 := by linarith [le_abs_self (burrMoment lam b 1)]
        refine ⟨?_, hA0⟩
        simp only [Function.mem_support]
        exact mul_ne_zero (pow_ne_zero 2 hAm) (hpdf A hA0).ne'
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      rw [Real.volume_Ioo]; norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with A hA
      exact mul_nonneg (sq_nonneg _) (hpdf A hA).le
  refine ⟨hpos, ?_⟩
  set X := 4 * (b - 2) * G ^ 2 / Real.pi - Real.Gamma (-3 / 2 + b) ^ 2
  have hH : Real.Gamma (-3 / 2 + b) = H := by rw [show (-3 / 2 + b) = b - 3 / 2 by ring]
  have hk : 0 < lam * Real.sqrt Real.pi / (2 * (b - 2) * G) := by positivity
  have hVe : burrMoment lam b 2 - (burrMoment lam b 1) ^ 2 = (lam * Real.sqrt Real.pi / (2 * (b - 2) * G)) ^ 2 * X := by
    rw [M2, M1]
    simp only [X, hH]
    field_simp
    rw [hP]; ring
  unfold burrSNR
  rw [hVe, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk.le, M1, hH]
  have hX : 0 < X := by
    have := hpos; rw [hVe] at this
    exact pos_of_mul_pos_right this (sq_nonneg _)
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  field_simp
