-- Prove2me | solution 1 for Arxiv2108_02600.kernel_log_sine_form
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:08:08.618608+00:00
-- url     : https://prove2.me/submissions/ff3b43ab-7963-4d08-a8bb-7f7df17ae14c

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology
open Arxiv2108_02600

lemma cutoff_lt_pi {x : ℝ} (h : cutoff x ≠ 0) : |x| < Real.pi := by
  unfold cutoff at h
  split_ifs at h with h1 h2
  · linarith [Real.pi_gt_three]
  · exact h2
  · exact absurd rfl h

lemma cutoff_eq_one {x : ℝ} (h : |x| ≤ 1) : cutoff x = 1 := by
  simp [cutoff, h]

lemma scalar_identity {x : ℝ} (hx : x ≠ 0) :
    1 / (2 * Real.pi) * Real.log (4 * Real.sin (x / 2) ^ 2) * (Real.pi * cutoff x) +
      ((1 - cutoff x) * Real.log |x| - cutoff x * Real.log (Real.sin (x / 2) / (x / 2))) =
    Real.log |x| := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  by_cases hc : cutoff x = 0
  · rw [hc]; field_simp; ring
  · have hlt := cutoff_lt_pi hc
    have hx2 : x / 2 ≠ 0 := by positivity
    have hs : Real.sin (x / 2) ≠ 0 := by
      intro h0
      have hab := abs_lt.mp hlt
      have := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos]) (by linarith)).mp h0
      exact hx2 this
    have l1 : Real.log (4 * Real.sin (x / 2) ^ 2) = 2 * Real.log 2 + 2 * Real.log (Real.sin (x / 2)) := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hs), Real.log_pow,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have l2 : Real.log (Real.sin (x / 2) / (x / 2)) = Real.log (Real.sin (x / 2)) - (Real.log x - Real.log 2) := by
      rw [Real.log_div hs hx2, Real.log_div hx (by norm_num)]
    rw [l1, l2, Real.log_abs]
    field_simp
    ring

theorem solution (A Bs Cs : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ s t : ℝ, s ≠ t → A s t = (Real.log |s - t| : ℂ) • Bs s t + Cs s t) :
    let B : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s t =>
      ((Real.pi * cutoff (s - t) : ℝ) : ℂ) • Bs s t
    let C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s t =>
      (((1 - cutoff (s - t)) * Real.log |s - t| -
          cutoff (s - t) * Real.log (Real.sin ((s - t) / 2) / ((s - t) / 2)) : ℝ) : ℂ) • Bs s t +
        Cs s t
    (∀ s t : ℝ, s ≠ t →
      A s t = ((1 / (2 * Real.pi) * Real.log (4 * Real.sin ((s - t) / 2) ^ 2) : ℝ) : ℂ) • B s t +
        C s t) ∧
    ∀ (s : ℝ) (Lb Lc : Matrix (Fin 2) (Fin 2) ℂ),
      Tendsto (Bs s) (𝓝[≠] s) (𝓝 Lb) → Tendsto (Cs s) (𝓝[≠] s) (𝓝 Lc) →
        Tendsto (B s) (𝓝[≠] s) (𝓝 ((Real.pi : ℂ) • Lb)) ∧ Tendsto (C s) (𝓝[≠] s) (𝓝 Lc) := by
  intro B C
  refine ⟨fun s t hst => ?_, fun s Lb Lc hB hC => ?_⟩
  · have hx : s - t ≠ 0 := sub_ne_zero.mpr hst
    simp only [B, C]
    rw [hA s t hst, smul_smul, ← add_assoc, ← add_smul]
    congr 2
    have h := congrArg (fun r : ℝ => (r : ℂ)) (scalar_identity hx)
    push_cast at h ⊢
    linear_combination -h
  · have hev : ∀ᶠ t in 𝓝[≠] s, cutoff (s - t) = 1 := by
      apply eventually_nhdsWithin_of_eventually_nhds
      have : ∀ᶠ t in 𝓝 s, |s - t| < 1 := by
        have hc : Continuous (fun t => |s - t|) := by fun_prop
        exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
      filter_upwards [this] with t ht
      exact cutoff_eq_one ht.le
    constructor
    · have := hB.const_smul (Real.pi : ℂ)
      apply this.congr'
      filter_upwards [hev] with t ht
      simp only [B, ht]; push_cast; ring_nf
    · have hsinc : Tendsto (fun t => Real.log (Real.sinc ((s - t) / 2))) (𝓝[≠] s) (𝓝 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds
        have hc : ContinuousAt (fun t => Real.log (Real.sinc ((s - t) / 2))) s := by
          apply ContinuousAt.log
          · exact (Real.continuous_sinc.comp (by fun_prop)).continuousAt
          · simp [Real.sinc_zero]
        simpa [Real.sinc_zero] using hc.tendsto
      have hscal : Tendsto (fun t => ((-Real.log (Real.sinc ((s - t) / 2)) : ℝ) : ℂ)) (𝓝[≠] s) (𝓝 0) := by
        have hn : Tendsto (fun t => -Real.log (Real.sinc ((s - t) / 2))) (𝓝[≠] s) (𝓝 0) := by
          simpa using hsinc.neg
        have := (Complex.continuous_ofReal.tendsto 0).comp hn
        simp only [Complex.ofReal_zero] at this
        exact this
      have hlim := (hscal.smul hB).add hC
      rw [zero_smul, zero_add] at hlim
      apply hlim.congr'
      filter_upwards [hev, self_mem_nhdsWithin] with t ht htne
      have hne : (s - t) / 2 ≠ 0 := by
        have : s - t ≠ 0 := sub_ne_zero.mpr (Ne.symm htne)
        positivity
      simp only [C, ht, Real.sinc_of_ne_zero hne]
      congr 2
      push_cast; ring

