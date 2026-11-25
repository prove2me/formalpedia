-- Prove2me | solution 1 for Arxiv2105_07250.uniform_window_moments_and_tent
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:40:51.040094+00:00
-- url     : https://prove2.me/submissions/177f3955-74c9-4bf0-96aa-1ae233a1e853

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace S71UW
open Arxiv2105_07250

lemma avg_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t0 T : ℝ) (hT : 0 < T)
    (g : ℝ → E) :
    ∫ τ, uniformWindowDensity t0 T τ • g τ = (1 / (2 * T)) • ∫ τ in (t0 - T)..(t0 + T), g τ := by
  have : (fun τ => uniformWindowDensity t0 T τ • g τ) =
      Set.indicator (Set.Icc (t0 - T) (t0 + T)) (fun τ => (1 / (2 * T)) • g τ) := by
    funext τ; simp only [uniformWindowDensity, Set.indicator_apply]; split_ifs <;> simp
  rw [this, integral_indicator measurableSet_Icc, integral_smul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]

lemma tent_int (L d : ℝ) (hL : 0 < L) (hd : 0 ≤ d) :
    ∫ y, boxcar L y * boxcar L (d - y) = max (L - d) 0 := by
  have : (fun y => boxcar L y * boxcar L (d - y)) =
      Set.indicator (Set.Icc (d - L / 2) (L / 2)) (1 : ℝ → ℝ) := by
    funext y
    simp only [boxcar, Set.indicator_apply, Set.mem_Icc, Pi.one_apply]
    by_cases ha : -(L/2) ≤ y ∧ y ≤ L/2 <;> by_cases hb : -(L/2) ≤ d - y ∧ d - y ≤ L/2 <;>
      by_cases hc : d - L/2 ≤ y ∧ y ≤ L/2 <;>
      (try rw [if_pos ha]) <;> (try rw [if_neg ha]) <;> (try rw [if_pos hb]) <;>
      (try rw [if_neg hb]) <;> (try rw [if_pos hc]) <;> (try rw [if_neg hc]) <;>
      simp only [mul_one, mul_zero] <;>
      first
      | rfl
      | (exfalso; apply hc; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2])
      | (exfalso; apply hb; constructor <;> linarith [hc.1, hc.2])
      | (exfalso; apply ha; constructor <;> linarith [hc.1, hc.2])
  rw [this, integral_indicator_one measurableSet_Icc, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal']
  congr 1; ring

lemma tent_eq (L d : ℝ) (hL : 0 < L) (hd : 0 ≤ d) : tentKernel L d = max (L - d) 0 := by
  unfold tentKernel heaviside
  rw [if_pos (by linarith), if_pos hd]
  by_cases h : 0 ≤ d - L
  · rw [if_pos h, max_eq_right (by linarith)]; ring
  · rw [if_neg h, max_eq_left (by linarith)]; ring

end S71UW

open Arxiv2105_07250 S71UW in
theorem solution (t0 T : ℝ) (hT : 0 < T) (v : Plane) (hv : v ≠ 0) :
    (∫ τ, uniformWindowDensity t0 T τ) = 1 ∧
    windowAvg (uniformWindowDensity t0 T) (fun τ => τ) = t0 ∧
    windowAvg (uniformWindowDensity t0 T) (fun τ => (τ - t0) ^ 2) = T ^ 2 / 3 ∧
    windowAvg (uniformWindowDensity t0 T) (fun τ => τ • v) = t0 • v ∧
    (∀ x' x'' : ℝ, ∫ y, boxcar (T * ‖v‖) y * boxcar (T * ‖v‖) (|x' - x''| - y) =
      tentKernel (T * ‖v‖) |x' - x''|) ∧
    (∀ x' x'' : ℝ, tentKernel (T * ‖v‖) |x' - x''| = max (T * ‖v‖ - |x' - x''|) 0) := by
  have hL : 0 < T * ‖v‖ := mul_pos hT (norm_pos_iff.2 hv)
  have hT2 : (2 * T) ≠ 0 := by positivity
  have h1 : (∫ τ, uniformWindowDensity t0 T τ) = 1 := by
    have := avg_eq t0 T hT (fun _ => (1 : ℝ))
    simp only [smul_eq_mul, mul_one] at this
    rw [this, intervalIntegral.integral_const, smul_eq_mul]; field_simp; ring
  have h2 : windowAvg (uniformWindowDensity t0 T) (fun τ => τ) = t0 := by
    unfold windowAvg
    rw [avg_eq t0 T hT, integral_id, smul_eq_mul]; field_simp; ring
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · unfold windowAvg
    rw [avg_eq t0 T hT, intervalIntegral.integral_comp_sub_right (fun τ => τ ^ 2), integral_pow,
      smul_eq_mul]
    field_simp; ring
  · unfold windowAvg
    have : (fun τ => uniformWindowDensity t0 T τ • τ • v) =
        fun τ => (uniformWindowDensity t0 T τ • τ) • v := by
      funext τ; rw [smul_smul, smul_eq_mul]
    rw [this, integral_smul_const]
    unfold windowAvg at h2; rw [h2]
  · intro x' x''
    rw [tent_int _ _ hL (abs_nonneg _), tent_eq _ _ hL (abs_nonneg _)]
  · intro x' x''
    exact tent_eq _ _ hL (abs_nonneg _)
