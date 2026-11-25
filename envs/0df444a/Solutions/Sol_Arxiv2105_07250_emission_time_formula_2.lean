-- Prove2me | solution 2 for Arxiv2105_07250.emission_time_formula
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:37:57.909973+00:00
-- url     : https://prove2.me/submissions/028119b2-e558-43c0-92eb-9e3814b3bf79

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open Arxiv2105_07250

lemma em_normsq (x v : Plane) (τ : ℝ) :
    ‖x - τ • v‖ ^ 2 = ‖x‖ ^ 2 - 2 * τ * inner ℝ x v + τ ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma em_q2 (c t : ℝ) (x v : Plane) (hK : 0 < c ^ 2 - ‖v‖ ^ 2) :
    q2 c t x v = (t - q1 c t x v) ^ 2 + ‖x - t • v‖ ^ 2 / (c ^ 2 - ‖v‖ ^ 2) := by
  unfold q2 q1
  rw [em_normsq]
  field_simp
  ring

lemma em_g (c t : ℝ) (x v : Plane) (hK : 0 < c ^ 2 - ‖v‖ ^ 2) (τ : ℝ) :
    c ^ 2 * (t - τ) ^ 2 - ‖x - τ • v‖ ^ 2 =
      (c ^ 2 - ‖v‖ ^ 2) * ((τ - q1 c t x v) ^ 2 - q2 c t x v) := by
  unfold q2 q1
  rw [em_normsq]
  field_simp
  ring

lemma em_anti (c t : ℝ) (x v : Plane) (hv : ‖v‖ < c) :
    StrictAnti (fun τ : ℝ => c * (t - τ) - ‖x - τ • v‖) := by
  intro a b hab
  have h1 : ‖x - a • v‖ ≤ ‖x - b • v‖ + (b - a) * ‖v‖ := by
    have : x - a • v = (x - b • v) + (b - a) • v := by
      rw [sub_smul]; abel
    rw [this]
    calc ‖(x - b • v) + (b - a) • v‖ ≤ ‖x - b • v‖ + ‖(b - a) • v‖ := norm_add_le _ _
      _ = ‖x - b • v‖ + (b - a) * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)]
  have h2 : (b - a) * ‖v‖ < (b - a) * c := mul_lt_mul_of_pos_left hv (sub_pos.mpr hab)
  simp only
  nlinarith

theorem solution (c : ℝ) (hc : 0 < c) (v : Plane) (hv : ‖v‖ < c) (x : Plane) (t : ℝ) :
    0 ≤ q2 c t x v ∧
    c * (t - emissionTime c t x v) = ‖x - emissionTime c t x v • v‖ ∧
    (∀ t' : ℝ, c * (t - t') = ‖x - t' • v‖ ↔ t' = emissionTime c t x v) ∧
    (∀ t' : ℝ, heaviside (t - t' - ‖x - t' • v‖ / c) =
      if t' ≤ emissionTime c t x v then 1 else 0) := by
  have hK : 0 < c ^ 2 - ‖v‖ ^ 2 := by
    have := norm_nonneg v
    nlinarith
  have hq := em_q2 c t x v hK
  have hq0 : 0 ≤ q2 c t x v := by
    rw [hq]; positivity
  set s := Real.sqrt (q2 c t x v) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = q2 c t x v := Real.sq_sqrt hq0
  have he : emissionTime c t x v = q1 c t x v - s := rfl
  -- e ≤ t
  have hle : emissionTime c t x v ≤ t := by
    rw [he]
    have : (q1 c t x v - t) ^ 2 ≤ s ^ 2 := by
      rw [hss, hq]
      have : 0 ≤ ‖x - t • v‖ ^ 2 / (c ^ 2 - ‖v‖ ^ 2) := by positivity
      nlinarith
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hroot : c * (t - emissionTime c t x v) = ‖x - emissionTime c t x v • v‖ := by
    have hg := em_g c t x v hK (emissionTime c t x v)
    rw [he] at hg ⊢
    rw [show (q1 c t x v - s - q1 c t x v) ^ 2 = s ^ 2 by ring, hss, sub_self, mul_zero] at hg
    have hl : 0 ≤ c * (t - (q1 c t x v - s)) := by
      apply mul_nonneg hc.le; rw [← he]; linarith
    have hsq : (c * (t - (q1 c t x v - s))) ^ 2 = ‖x - (q1 c t x v - s) • v‖ ^ 2 := by
      rw [mul_pow]; linarith
    exact (sq_eq_sq₀ hl (norm_nonneg _)).mp hsq
  have hanti := em_anti c t x v hv
  have hphi0 : c * (t - emissionTime c t x v) - ‖x - emissionTime c t x v • v‖ = 0 := by
    rw [hroot, sub_self]
  refine ⟨hq0, hroot, fun t' => ?_, fun t' => ?_⟩
  · constructor
    · intro h
      apply hanti.injective
      simp only
      rw [h, sub_self, hphi0]
    · rintro rfl; exact hroot
  · unfold heaviside
    have key : 0 ≤ t - t' - ‖x - t' • v‖ / c ↔ t' ≤ emissionTime c t x v := by
      have e1 : t - t' - ‖x - t' • v‖ / c = (c * (t - t') - ‖x - t' • v‖) / c := by
        field_simp
      rw [e1, div_nonneg_iff]
      constructor
      · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · by_contra hlt
          push_neg at hlt
          have := hanti hlt
          simp only at this
          linarith
        · linarith
      · intro h
        left
        refine ⟨?_, hc.le⟩
        rcases h.lt_or_eq with hlt | heq
        · have := hanti hlt
          simp only at this
          linarith
        · rw [heq]; linarith
    by_cases h : t' ≤ emissionTime c t x v
    · rw [if_pos (key.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

