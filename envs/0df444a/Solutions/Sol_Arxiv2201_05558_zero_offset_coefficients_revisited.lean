-- Prove2me | solution 1 for Arxiv2201_05558.zero_offset_coefficients_revisited
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:40:06.926302+00:00
-- url     : https://prove2.me/submissions/f5fbbe50-d67e-4c7d-b933-d91eb74bab1e

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology
open Arxiv2201_05558

lemma zo_unique (g G g' : ℝ → ℂ) (L : ℂ)
    (hg : ∀ z : ℝ, 0 < z → HasDerivAt g (g' z) z) (hG : ∀ z : ℝ, 0 < z → HasDerivAt G (g' z) z)
    (hlim : Tendsto g (𝓝[>] 0) (𝓝 L)) (hGlim : Tendsto G (𝓝[>] 0) (𝓝 L)) :
    ∀ z : ℝ, 0 < z → g z = G z := by
  intro z hz
  set h : ℝ → ℂ := fun w => g w - G w with hh
  have hd : ∀ w ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt h 0 (Set.Ioi 0) w := by
    intro w hw
    have := (hg w hw).sub (hG w hw)
    rw [sub_self] at this
    exact this.hasDerivWithinAt
  have hconst : ∀ w ∈ Set.Ioi (0 : ℝ), h w = h z := by
    intro w hw
    have := (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun _ _ => by simp : ∀ x ∈ Set.Ioi (0 : ℝ), ‖(0 : ℂ)‖ ≤ 0) hz hw
    rw [zero_mul] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have h1 : Tendsto h (𝓝[>] 0) (𝓝 (L - L)) := hlim.sub hGlim
  have h2 : Tendsto h (𝓝[>] 0) (𝓝 (h z)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hconst w hw).symm
  have := tendsto_nhds_unique h2 h1
  rw [sub_self] at this
  exact sub_eq_zero.mp this

lemma zo_lim (f : ℝ → ℝ) (hf : Continuous f) (L : ℝ) (h0 : f 0 = L) :
    Tendsto (fun z => ((f z : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (L : ℂ)) := by
  have h1 : Tendsto (fun z => ((f z : ℝ) : ℂ)) (𝓝 0) (𝓝 ((f 0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp hf).tendsto 0
  rw [h0] at h1
  exact h1.mono_left nhdsWithin_le_nhds

theorem solution (ω0 c0 D ρ0 : ℝ) (hω0 : 0 < ω0) (hc0 : 0 < c0)
    (hρ0 : 0 < ρ0) (a b c d : ℝ → ℂ) (hode : SolvesCoefODE ω0 c0 D 0 a b c d)
    (ha : Tendsto a (𝓝[>] 0) (𝓝 0))
    (hb : Tendsto b (𝓝[>] 0) (𝓝 ((1 / (4 * ρ0 ^ 2) : ℝ) : ℂ)))
    (hc : Tendsto c (𝓝[>] 0) (𝓝 0)) (hd : Tendsto d (𝓝[>] 0) (𝓝 0)) :
    ∀ z : ℝ, 0 < z → a z = 0 ∧
      b z = ((ω0 ^ 2 * D * z / (16 * c0 ^ 2) + 1 / (4 * ρ0 ^ 2) : ℝ) : ℂ) ∧
      c z = ((ω0 * D * z ^ 2 / (16 * c0) : ℝ) : ℂ) ∧
      d z = ((D * z ^ 3 / 48 : ℝ) : ℂ) := by
  intro z hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine zo_unique a (fun _ => 0) _ 0 (fun w hw => (hode w hw).1)
      (fun w hw => (hasDerivAt_const w (0 : ℂ)).congr_deriv (by simp)) ha tendsto_const_nhds z hz
  · refine zo_unique b (fun w => ((ω0 ^ 2 * D * w / (16 * c0 ^ 2) + 1 / (4 * ρ0 ^ 2) : ℝ) : ℂ)) _ _
      (fun w hw => (hode w hw).2.1) (fun w hw => ?_) hb
      (zo_lim _ (by fun_prop) _ (by simp)) z hz
    have := ((((hasDerivAt_id' w).const_mul (ω0 ^ 2 * D)).div_const (16 * c0 ^ 2)).add_const
      (1 / (4 * ρ0 ^ 2))).ofReal_comp
    refine this.congr_deriv ?_
    simp
  · refine zo_unique c (fun w => ((ω0 * D * w ^ 2 / (16 * c0) : ℝ) : ℂ)) _ _
      (fun w hw => (hode w hw).2.2.1) (fun w hw => ?_) hc
      (by have h := zo_lim (fun w => ω0 * D * w ^ 2 / (16 * c0)) (by fun_prop) 0 (by simp); rw [Complex.ofReal_zero] at h; exact h) z hz
    have := (((hasDerivAt_pow 2 w).const_mul (ω0 * D)).div_const (16 * c0)).ofReal_comp
    refine this.congr_deriv ?_
    simp only [zero_div, mul_zero, Complex.ofReal_zero, add_zero, zero_mul]
    push_cast
    field_simp
    ring
  · refine zo_unique d (fun w => ((D * w ^ 3 / 48 : ℝ) : ℂ)) _ _
      (fun w hw => (hode w hw).2.2.2) (fun w hw => ?_) hd
      (by have h := zo_lim (fun w => D * w ^ 3 / 48) (by fun_prop) 0 (by simp); rw [Complex.ofReal_zero] at h; exact h) z hz
    have := (((hasDerivAt_pow 3 w).const_mul D).div_const 48).ofReal_comp
    refine this.congr_deriv ?_
    simp only [zero_div, mul_zero, Complex.ofReal_zero, add_zero, zero_mul]
    push_cast
    ring

