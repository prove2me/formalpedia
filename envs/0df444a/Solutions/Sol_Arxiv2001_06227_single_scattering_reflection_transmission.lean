-- Prove2me | solution 1 for Arxiv2001_06227.single_scattering_reflection_transmission
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T03:55:39.249799+00:00
-- url     : https://prove2.me/submissions/6d8a4437-6135-4aff-a870-932b5ce1a074

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

open MeasureTheory Filter Topology Set
namespace S77SS
open Arxiv2001_06227

lemma ss_heav_meas : Measurable heaviside := by
  unfold heaviside
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma ss_heav_ind (t : ℝ) : heaviside t = (Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) t := by
  unfold heaviside; by_cases h : 0 ≤ t <;> simp [h, Set.indicator]

lemma ss_heav_bd (t : ℝ) : 0 ≤ heaviside t ∧ heaviside t ≤ 1 := by
  unfold heaviside; split_ifs <;> norm_num

-- inner s' integral
lemma ss_inner (muS b : ℝ) (hmuS : 0 < muS) (hb : 0 ≤ b) :
    ∫ s' in Ioi (0:ℝ), muS * Real.exp (-(muS * s')) * heaviside (s' - b) = Real.exp (-(muS * b)) := by
  have h1 : ∀ s', muS * Real.exp (-(muS * s')) * heaviside (s' - b)
      = (Ici b).indicator (fun s' => muS * Real.exp ((-muS) * s')) s' := by
    intro s'
    rw [ss_heav_ind]
    by_cases h : b ≤ s'
    · simp [Set.indicator, h, sub_nonneg.2 h, neg_mul]
    · have : ¬ 0 ≤ s' - b := by linarith
      simp [Set.indicator, h, this]
  simp_rw [h1]
  rw [setIntegral_indicator measurableSet_Ici]
  have : Ioi (0:ℝ) ∩ Ici b = Ici b ∩ Ioi 0 := inter_comm _ _
  rcases eq_or_lt_of_le hb with h | h
  · subst h
    rw [inter_eq_left.2 Ioi_subset_Ici_self, integral_const_mul, integral_exp_mul_Ioi (by linarith)]
    field_simp
  · rw [inter_eq_right.2 (Ici_subset_Ioi.2 h), integral_Ici_eq_integral_Ioi, integral_const_mul,
      integral_exp_mul_Ioi (by linarith)]
    field_simp

-- outer s integral
lemma ss_outer (muS k L : ℝ) (hk : k ≠ 0) (hL : 0 < L) :
    ∫ s in Ioi (0:ℝ), heaviside (L - s) * (muS * Real.exp (-(k * s)))
      = muS * (1 - Real.exp (-(k * L))) / k := by
  have h1 : ∀ s, heaviside (L - s) * (muS * Real.exp (-(k * s)))
      = (Iic L).indicator (fun s => muS * Real.exp (-(k * s))) s := by
    intro s
    rw [ss_heav_ind]
    by_cases h : s ≤ L
    · simp [Set.indicator, h, sub_nonneg.2 h]
    · have : ¬ 0 ≤ L - s := by linarith
      simp [Set.indicator, h, this]
  simp_rw [h1]
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, ← intervalIntegral.integral_of_le hL.le]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun t => Real.exp (-t)) hk,
    intervalIntegral.integral_comp_neg, integral_exp]
  simp
  field_simp

lemma ss_neg (f : ℝ → ℝ) : ∫ x in Ioo (-1:ℝ) 0, f x = ∫ x in Ioo (0:ℝ) 1, f (-x) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num), ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_comp_neg]
  norm_num


lemma ss_swap (muS a b : ℝ) (hmuS : 0 < muS) (q : ℝ → ℝ) (G : ℝ → ℝ → ℝ)
    (hG : Measurable (fun z : ℝ × ℝ => G z.1 z.2))
    (hbd : ∀ s ∈ Ioi (0:ℝ), ∀ μ ∈ Ioo a b, 0 ≤ G s μ ∧ G s μ ≤ 1)
    (hq : IntegrableOn q (Ioo a b)) (hq0 : ∀ μ, 0 ≤ q μ) :
    ∫ s in Ioi (0:ℝ), ∫ μ in Ioo a b, muS * Real.exp (-(muS * s)) * (q μ * G s μ)
      = ∫ μ in Ioo a b, ∫ s in Ioi (0:ℝ), muS * Real.exp (-(muS * s)) * (q μ * G s μ) := by
  apply integral_integral_swap
  have hf : IntegrableOn (fun s => muS * Real.exp (-(muS * s))) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 hmuS).const_mul muS
    simp only [neg_mul] at this; exact this
  have hbound := Integrable.mul_prod hf hq
  refine hbound.mono' ?_ ?_
  · have hqm : AEStronglyMeasurable (fun z : ℝ × ℝ => q z.2)
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo a b))) :=
      hq.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    exact (by fun_prop : Measurable fun z : ℝ × ℝ => muS * Real.exp (-(muS * z.1))).aestronglyMeasurable.mul
      (hqm.mul hG.aestronglyMeasurable)
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with z hz
    obtain ⟨hs, hμ⟩ := hz
    obtain ⟨g0, g1⟩ := hbd z.1 hs z.2 hμ
    show ‖muS * Real.exp (-(muS * z.1)) * (q z.2 * G z.1 z.2)‖ ≤ _
    rw [Real.norm_eq_abs]
    have ha : 0 ≤ muS * Real.exp (-(muS * z.1)) := by positivity
    rw [abs_of_nonneg (mul_nonneg ha (mul_nonneg (hq0 _) g0))]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hq0 _) g1) ha

lemma ss_R (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p)
    (muS muA L : ℝ) (hmuS : 0 < muS) (hmuA : 0 < muA) (hL : 0 < L) :
    slabReflect p muS muA L = ∫ μ in Set.Ioo (0 : ℝ) 1, muS / (muA + muS) * (μ / (μ + 1)) * p (-μ) 1 *
      (1 - Real.exp (-((muA + muS) * L * ((μ + 1) / μ)))) := by
  unfold slabReflect
  set G : ℝ → ℝ → ℝ := fun s μ =>
    Real.exp (-(muA * (s - s / μ))) * heaviside (L - s) * Real.exp (-(muS * (-(s / μ)))) with hGdef
  have step1 : ∀ s ∈ Ioi (0:ℝ), muS * Real.exp (-(muS * s)) *
      (∫ μ in Set.Ioo (-1 : ℝ) 0, p μ 1 *
        ∫ s' in Set.Ioi (0 : ℝ), muS * Real.exp (-(muS * s')) *
          Real.exp (-(muA * (s - s / μ))) * heaviside (L - s) * heaviside (s' + s / μ))
      = ∫ μ in Ioo (-1:ℝ) 0, muS * Real.exp (-(muS * s)) * (p μ 1 * G s μ) := by
    intro s hs
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo (fun μ hμ => ?_)
    have hb : 0 ≤ -(s / μ) := neg_nonneg.2 (div_neg_of_pos_of_neg hs hμ.2).le
    have : (fun s' => muS * Real.exp (-(muS * s')) * Real.exp (-(muA * (s - s / μ))) *
        heaviside (L - s) * heaviside (s' + s / μ)) = fun s' =>
        (Real.exp (-(muA * (s - s / μ))) * heaviside (L - s)) *
          (muS * Real.exp (-(muS * s')) * heaviside (s' - (-(s / μ)))) := by
      funext s'; rw [show s' + s / μ = s' - (-(s / μ)) by ring]; ring
    rw [this, integral_const_mul, ss_inner muS _ hmuS hb]
  rw [setIntegral_congr_fun measurableSet_Ioi step1]
  have hq : IntegrableOn (fun μ => p μ 1) (Ioo (-1) 0) :=
    hp.2.1.mono_set (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by norm_num)))
  have hH := ss_heav_meas
  rw [ss_swap muS (-1) 0 hmuS (fun μ => p μ 1) G (by simp only [hGdef]; fun_prop) ?_ hq (fun μ => hp.1 μ 1)]
  rotate_left
  · intro s hs μ hμ
    have hs' : (0:ℝ) < s := hs
    have hneg : s / μ < 0 := div_neg_of_pos_of_neg hs' hμ.2
    obtain ⟨h0, h1⟩ := ss_heav_bd (L - s)
    simp only [hGdef]
    refine ⟨by positivity, ?_⟩
    have e1 : Real.exp (-(muA * (s - s / μ))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have e2 : Real.exp (-(muS * (-(s / μ)))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    exact mul_le_one₀ (mul_le_one₀ e1 h0 h1) (Real.exp_pos _).le e2
  have step3 : ∀ μ ∈ Ioo (-1:ℝ) 0, ∫ s in Ioi (0:ℝ), muS * Real.exp (-(muS * s)) * (p μ 1 * G s μ)
      = p μ 1 * (muS * (1 - Real.exp (-((muA + muS) * (1 - 1 / μ) * L))) /
          ((muA + muS) * (1 - 1 / μ))) := by
    intro μ hμ
    have hk : (muA + muS) * (1 - 1 / μ) ≠ 0 := by
      have : 1 / μ < 0 := by rw [one_div]; exact inv_lt_zero.2 hμ.2
      have : 0 < (muA + muS) * (1 - 1 / μ) := mul_pos (by linarith) (by linarith)
      exact this.ne'
    have key : ∀ s, muS * Real.exp (-(muS * s)) * (p μ 1 * G s μ)
        = p μ 1 * (heaviside (L - s) * (muS * Real.exp (-((muA + muS) * (1 - 1 / μ) * s)))) := by
      intro s
      have : Real.exp (-(muS * s)) * Real.exp (-(muA * (s - s / μ))) * Real.exp (-(muS * (-(s / μ))))
          = Real.exp (-((muA + muS) * (1 - 1 / μ) * s)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      simp only [hGdef]
      linear_combination (muS * p μ 1 * heaviside (L - s)) * this
    simp_rw [key]
    rw [integral_const_mul, ss_outer muS _ L hk hL]
  rw [setIntegral_congr_fun measurableSet_Ioo step3, ss_neg]
  refine setIntegral_congr_fun measurableSet_Ioo (fun μ hμ => ?_)
  have hμ0 : μ ≠ 0 := hμ.1.ne'
  have h1 : (muA + muS) * (1 - 1 / -μ) * L = (muA + muS) * L * ((μ + 1) / μ) := by
    field_simp; ring
  have h2 : (muA + muS) * (1 - 1 / -μ) = (muA + muS) * (μ + 1) / μ := by
    field_simp; ring
  rw [h1, h2]
  have : μ + 1 ≠ 0 := by linarith [hμ.1]
  have : muA + muS ≠ 0 := by linarith
  field_simp

lemma ss_T (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p)
    (muS muA L : ℝ) (hmuS : 0 < muS) (hmuA : 0 < muA) (hL : 0 < L) :
    slabTransmit p muS muA L = Real.exp (-((muA + muS) * L)) +
      ∫ μ in Set.Ioo (0 : ℝ) 1, muS / (muA + muS) * (μ / (μ - 1)) * p μ 1 *
      (1 - Real.exp (-((muA + muS) * L * ((μ - 1) / μ)))) *
        Real.exp (-((muA + muS) * L / μ)) := by
  unfold slabTransmit
  congr 1
  set G : ℝ → ℝ → ℝ := fun s μ =>
    Real.exp (-(muA * (s + (L - s) / μ))) * heaviside (L - s) * Real.exp (-(muS * ((L - s) / μ)))
    with hGdef
  have step1 : ∀ s ∈ Ioi (0:ℝ), muS * Real.exp (-(muS * s)) *
      (∫ μ in Set.Ioo (0 : ℝ) 1, p μ 1 *
        ∫ s' in Set.Ioi (0 : ℝ), muS * Real.exp (-(muS * s')) *
          Real.exp (-(muA * (s + (L - s) / μ))) * heaviside (L - s) *
            heaviside (s' - (L - s) / μ))
      = ∫ μ in Ioo (0:ℝ) 1, muS * Real.exp (-(muS * s)) * (p μ 1 * G s μ) := by
    intro s hs
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo (fun μ hμ => ?_)
    simp only [hGdef]
    by_cases hsL : s ≤ L
    · have hb : 0 ≤ (L - s) / μ := div_nonneg (by linarith) hμ.1.le
      have : (fun s' => muS * Real.exp (-(muS * s')) * Real.exp (-(muA * (s + (L - s) / μ))) *
          heaviside (L - s) * heaviside (s' - (L - s) / μ)) = fun s' =>
          (Real.exp (-(muA * (s + (L - s) / μ))) * heaviside (L - s)) *
            (muS * Real.exp (-(muS * s')) * heaviside (s' - (L - s) / μ)) := by
        funext s'; ring
      rw [this, integral_const_mul, ss_inner muS _ hmuS hb]
    · have h0 : heaviside (L - s) = 0 := by unfold heaviside; rw [if_neg]; linarith
      simp [h0]
  rw [setIntegral_congr_fun measurableSet_Ioi step1]
  have hq : IntegrableOn (fun μ => p μ 1) (Ioo 0 1) :=
    hp.2.1.mono_set (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by norm_num) le_rfl))
  have hH := ss_heav_meas
  rw [ss_swap muS 0 1 hmuS (fun μ => p μ 1) G (by simp only [hGdef]; fun_prop) ?_ hq (fun μ => hp.1 μ 1)]
  rotate_left
  · intro s hs μ hμ
    have hs' : (0:ℝ) < s := hs
    obtain ⟨h0, h1⟩ := ss_heav_bd (L - s)
    simp only [hGdef]
    refine ⟨by positivity, ?_⟩
    by_cases hsL : s ≤ L
    · have hb : 0 ≤ (L - s) / μ := div_nonneg (by linarith) hμ.1.le
      have e1 : Real.exp (-(muA * (s + (L - s) / μ))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have e2 : Real.exp (-(muS * ((L - s) / μ))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      exact mul_le_one₀ (mul_le_one₀ e1 h0 h1) (Real.exp_pos _).le e2
    · have h0 : heaviside (L - s) = 0 := by unfold heaviside; rw [if_neg]; linarith
      simp [h0]
  have step3 : ∀ μ ∈ Ioo (0:ℝ) 1, ∫ s in Ioi (0:ℝ), muS * Real.exp (-(muS * s)) * (p μ 1 * G s μ)
      = (p μ 1 * Real.exp (-((muA + muS) * L / μ))) *
        (muS * (1 - Real.exp (-((muA + muS) * (1 - 1 / μ) * L))) /
          ((muA + muS) * (1 - 1 / μ))) := by
    intro μ hμ
    have hk : (muA + muS) * (1 - 1 / μ) ≠ 0 := by
      have : 1 < 1 / μ := by rw [lt_one_div (by norm_num) hμ.1]; simpa using hμ.2
      have : (muA + muS) * (1 - 1 / μ) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
      exact this.ne
    have key : ∀ s, muS * Real.exp (-(muS * s)) * (p μ 1 * G s μ)
        = (p μ 1 * Real.exp (-((muA + muS) * L / μ))) *
          (heaviside (L - s) * (muS * Real.exp (-((muA + muS) * (1 - 1 / μ) * s)))) := by
      intro s
      have : Real.exp (-(muS * s)) * Real.exp (-(muA * (s + (L - s) / μ))) *
          Real.exp (-(muS * ((L - s) / μ)))
          = Real.exp (-((muA + muS) * L / μ)) * Real.exp (-((muA + muS) * (1 - 1 / μ) * s)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      simp only [hGdef]
      linear_combination (muS * p μ 1 * heaviside (L - s)) * this
    simp_rw [key]
    rw [integral_const_mul, ss_outer muS _ L hk hL]
  rw [setIntegral_congr_fun measurableSet_Ioo step3]
  refine setIntegral_congr_fun measurableSet_Ioo (fun μ hμ => ?_)
  have hμ0 : μ ≠ 0 := hμ.1.ne'
  have hμ1 : μ - 1 ≠ 0 := by linarith [hμ.2]
  have h1 : (muA + muS) * (1 - 1 / μ) * L = (muA + muS) * L * ((μ - 1) / μ) := by
    field_simp
  have h2 : (muA + muS) * (1 - 1 / μ) = (muA + muS) * (μ - 1) / μ := by
    field_simp
  rw [h1, h2]
  have : muA + muS ≠ 0 := by linarith
  field_simp

end S77SS

open Arxiv2001_06227 S77SS in
theorem solution (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p)
    (muS muA L : ℝ) (hmuS : 0 < muS) (hmuA : 0 < muA) (hL : 0 < L) :
    slabReflect p muS muA L + slabTransmit p muS muA L = slabRT p muS muA L := by
  rw [ss_R p hp muS muA L hmuS hmuA hL, ss_T p hp muS muA L hmuS hmuA hL]
  unfold slabRT
  ring

