-- Prove2me | Definitions.Def_dusart_psi_433_20261014_LowHeight
-- name    : dusart_psi_433_20261014_LowHeight
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:21:49.977026+00:00
-- url     : https://prove2.me/theorems/bd6a62f8-75b9-43d9-8db1-6054be94f2a2
-- title:
--   Dusart smoothing: Low Height
-- statement:
--   This module gives the complete low height component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZetaGrowth
import Definitions.Def_dusart_psi_433_20261014_Mellin
open scoped BigOperators
open Real Complex Set MeasureTheory
namespace DusartSmoothing.LowHeight

lemma exp_neg_three_lt : Real.exp (-3) < (1 / 20 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have h20 : (20 : ℝ) < Real.exp 3 := by linarith
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 3)).2
  linarith

lemma theta_kernel_bound (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ HurwitzZeta.evenKernel 0 x - 1 ∧
    HurwitzZeta.evenKernel 0 x - 1 ≤ (9 / 4 : ℝ) * Real.exp (-3 * x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have htheta : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * x))
      (HurwitzZeta.evenKernel 0 x - 1) := by
    simpa [zero_mul, mul_zero, Real.cos_zero, mul_one,
      HurwitzZeta.evenKernel_eq_cosKernel_of_zero] using
      HurwitzZeta.hasSum_nat_cosKernel₀ 0 hx0
  let q := Real.exp (-3 * x)
  have hq0 : 0 < q := Real.exp_pos _
  have hq20 : q < (1 / 20 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : -3 * x ≤ -3)).trans_lt exp_neg_three_lt
  have hq1 : q < 1 := by linarith
  have hgeo := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (2 * q)
  have hterm (n : ℕ) :
      2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * x) ≤
      (2 * q) * q^n := by
    have hn : (1 : ℝ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hsq : (n + 1 : ℝ) ≤ (n + 1 : ℝ)^2 := by nlinarith
    have hp : 3 * (n + 1 : ℝ) ≤ Real.pi * (n + 1 : ℝ)^2 := by
      nlinarith [Real.pi_gt_three]
    have he : -Real.pi * (n + 1 : ℝ)^2 * x ≤ (n + 1 : ℝ) * (-3 * x) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hx0.le]
    calc
      2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * x) ≤
          2 * Real.exp ((n + 1 : ℝ) * (-3 * x)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) zero_le_two
      _ = (2 * q) * q^n := by
        rw [show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast; rfl, Real.exp_nat_mul]
        simp only [q, pow_succ]
        ring
  have hsum := htheta.summable.tsum_le_tsum hterm hgeo.summable
  rw [htheta.tsum_eq, hgeo.tsum_eq] at hsum
  constructor
  · rw [← htheta.tsum_eq]
    exact tsum_nonneg (fun n => mul_nonneg zero_le_two (Real.exp_pos _).le)
  · apply hsum.trans
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (by linarith : 0 < 1 - q)).2
    nlinarith

noncomputable def upperKernel : ℝ → ℂ :=
  (Ioi 1).indicator (fun x => (HurwitzZeta.evenKernel 0 x : ℂ) - 1)

lemma upper_integrand_bound (z : ℂ) (hz : z.re ≤ 1) (x : ℝ) (hx : 1 < x) :
    ‖(x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1)‖ ≤
      (9 / 4 : ℝ) * Real.exp (-3 * x) := by
  have hx0 : 0 < x := by linarith
  have hk := theta_kernel_bound x hx.le
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hp : x ^ (z - 1).re ≤ (1 : ℝ) :=
    Real.rpow_le_one_of_one_le_of_nonpos hx.le (by simpa using sub_nonpos.mpr hz)
  have hn : ‖(HurwitzZeta.evenKernel 0 x : ℂ) - 1‖ =
      HurwitzZeta.evenKernel 0 x - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hk.1]
  rw [hn]
  exact (mul_le_of_le_one_left hk.1 hp).trans hk.2

lemma upper_integrand_integrable (z : ℂ) (hz : z.re ≤ 1) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1)) (Ioi 1) := by
  have hd : IntegrableOn (fun x : ℝ => (9 / 4 : ℝ) * Real.exp (-3 * x)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) 1).const_mul (9 / 4)
  have hc : ContinuousOn (fun x : ℝ =>
      (x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1)) (Ioi 1) := by
    have hpow : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (z - 1)) (Ioi 1) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      exact Complex.continuousAt_ofReal_cpow_const x (z - 1) (Or.inr hx0.ne')
    have hk : ContinuousOn (fun x : ℝ => (HurwitzZeta.evenKernel 0 x : ℂ) - 1) (Ioi 1) :=
      (Complex.continuous_ofReal.comp_continuousOn
        ((HurwitzZeta.continuousOn_evenKernel 0).mono
          (fun x hx => by simp only [mem_Ioi] at *; linarith))).sub continuousOn_const
    exact hpow.smul hk
  exact hd.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_mem measurableSet_Ioi |>.mono fun x hx => upper_integrand_bound z hz x hx)

lemma upper_mellin_convergent (z : ℂ) (hz : z.re ≤ 1) :
    MellinConvergent upperKernel z := by
  unfold MellinConvergent upperKernel
  simp_rw [← indicator_smul]
  exact ((upper_integrand_integrable z hz).integrable_indicator measurableSet_Ioi).integrableOn

lemma upper_mellin_bound (z : ℂ) (hz : z.re ≤ 1) :
    ‖mellin upperKernel z‖ ≤ (3 / 80 : ℝ) := by
  have hd : IntegrableOn (fun x : ℝ => (9 / 4 : ℝ) * Real.exp (-3 * x)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) 1).const_mul (9 / 4)
  have hle := norm_integral_le_of_norm_le hd
    (ae_restrict_mem measurableSet_Ioi |>.mono fun x hx => upper_integrand_bound z hz x hx)
  have hrepr : mellin upperKernel z =
      ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1) := by
    unfold mellin upperKernel
    simp_rw [← indicator_smul, setIntegral_indicator measurableSet_Ioi]
    rw [inter_eq_right.mpr (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro x hx
      simp only [mem_Ioi] at *
      linarith)]
  rw [hrepr]
  apply hle.trans
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) 1]
  have he := exp_neg_three_lt
  norm_num at *
  linarith

lemma modif_sub_upper (x : ℝ) (hx : 0 < x) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x - upperKernel x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) • upperKernel (x⁻¹) := by
  rcases lt_trichotomy 1 x with h | h | h
  · have hi : x⁻¹ ≤ 1 := (inv_le_one₀ hx).2 h.le
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, upperKernel,
      h, not_lt.mpr hi, not_lt.mpr h.le]
  · subst x
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, upperKernel]
  · have hi : 1 < x⁻¹ := (one_lt_inv₀ hx).2 h
    simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, upperKernel,
      Pi.add_apply, Function.comp_apply, ite_true, one_mul, smul_eq_mul, mul_one]
    simp only [indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from not_lt.mpr h.le),
      indicator_of_mem (show x ∈ Ioo 0 1 from ⟨hx, h⟩),
      indicator_of_mem (show x⁻¹ ∈ Ioi (1 : ℝ) from hi)]
    simp only [zero_add, sub_zero]
    have hf : (HurwitzZeta.evenKernel 0 x : ℂ) =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * (HurwitzZeta.evenKernel 0 (x⁻¹) : ℂ) := by
      rw [HurwitzZeta.evenKernel_functional_equation, ← HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
      push_cast
      have hc : ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
        simpa using Complex.ofReal_cpow hx.le (1 / 2 : ℝ)
      simpa only [one_div, Complex.cpow_neg] using!
        congrArg (fun w : ℂ => w⁻¹ * (HurwitzZeta.evenKernel 0 (x⁻¹) : ℂ)) hc
    have hp : ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
      simpa using Complex.ofReal_cpow hx.le (-(1 / 2 : ℝ))
    rw [hf, hp]
    ring

lemma completed_mellin_split (s : ℂ) (hσ : s.re ≤ 1) :
    completedRiemannZeta₀ s =
      (mellin upperKernel (s / 2) + mellin upperKernel ((1 - s) / 2)) / 2 := by
  have hz : (s / 2).re ≤ 1 := by simp; linarith
  have hc : MellinConvergent (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) :=
    ((HurwitzZeta.hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin (s / 2)).1
  have hm := (hasMellin_sub hc (upper_mellin_convergent (s / 2) hz)).2
  have he :
      mellin (fun x => (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x - upperKernel x) (s / 2) =
        mellin upperKernel ((1 - s) / 2) := by
    calc
      _ = mellin (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) • upperKernel (x⁻¹)) (s / 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [modif_sub_upper x hx]
      _ = mellin (fun x : ℝ => upperKernel (x⁻¹)) (s / 2 + -(1 / 2 : ℂ)) :=
        mellin_cpow_smul _ _ _
      _ = mellin upperKernel (-(s / 2 + -(1 / 2 : ℂ))) := mellin_comp_inv _ _
      _ = _ := by congr 1; ring
  rw [he] at hm
  unfold completedRiemannZeta₀ HurwitzZeta.completedHurwitzZetaEven₀ WeakFEPair.Λ₀
  congr 1
  linear_combination -hm

lemma completed_entire_bound (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ (3 / 80 : ℝ) := by
  rw [completed_mellin_split s hσ1, norm_div]
  have h1 := upper_mellin_bound (s / 2) (by simp; linarith)
  have h2 := upper_mellin_bound ((1 - s) / 2) (by simp; linarith)
  have hn := norm_add_le (mellin upperKernel (s / 2)) (mellin upperKernel ((1 - s) / 2))
  norm_num
  linarith

theorem zeta_nonzero_small_height (s : ℂ) (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1)
    (ht0 : 0 < s.im) (ht4 : s.im ≤ 4) : riemannZeta s ≠ 0 := by
  have hs : s ≠ 0 := by intro h; subst s; simp at ht0
  have hs1 : 1 - s ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hn1 : ‖s‖ ≤ 5 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hσ0.le, abs_of_nonneg ht0.le] at h
    linarith
  have hn2 : ‖1 - s‖ ≤ 5 := by
    have h := Complex.norm_le_abs_re_add_abs_im (1 - s)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, abs_neg] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hσ1), abs_of_nonneg ht0.le] at h
    linarith
  intro hz
  have hzC : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs] at hz
    rcases (div_eq_zero_iff).mp hz with h | h
    · exact h
    · exact (Complex.Gammaℝ_ne_zero_of_re_pos hσ0 h).elim
  have hid : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
    have h := completedRiemannZeta_eq s
    rw [hzC] at h
    linear_combination -h
  have he : s * (1 - s) * completedRiemannZeta₀ s = 1 := by
    rw [hid]
    field_simp
    ring
  have hsmall := completed_entire_bound s hσ0.le hσ1
  have hn : ‖s * (1 - s) * completedRiemannZeta₀ s‖ < 1 := by
    calc
      _ = ‖s‖ * ‖1 - s‖ * ‖completedRiemannZeta₀ s‖ := by rw [norm_mul, norm_mul]
      _ ≤ 5 * 5 * (3 / 80 : ℝ) := by gcongr
      _ < 1 := by norm_num
  rw [he] at hn
  norm_num at hn

end DusartSmoothing.LowHeight


