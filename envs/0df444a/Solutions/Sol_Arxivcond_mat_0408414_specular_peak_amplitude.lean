-- Prove2me | solution 1 for Arxivcond_mat_0408414.specular_peak_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:40:31.621797+00:00
-- url     : https://prove2.me/submissions/a0e5ee44-b6f5-4e22-be54-84c5d72274ea

import Mathlib
import Definitions.Def_Arxivcond_mat_0408414_Basic

set_option autoImplicit false

open MeasureTheory Real

namespace S74SP

lemma levy0 (α : ℝ) (hα : 0 < α) :
    (∫ k : ℝ, Complex.exp (((k * 0 : ℝ) : ℂ) * Complex.I) * ((Real.exp (-(|k| ^ α)) : ℝ) : ℂ)).re /
      (2 * π) = Real.Gamma (1 / α) / (α * π) := by
  have h1 : (fun k : ℝ => Complex.exp (((k * 0 : ℝ) : ℂ) * Complex.I) * ((Real.exp (-(|k| ^ α)) : ℝ) : ℂ)) =
      fun k => ((Real.exp (-(|k| ^ α)) : ℝ) : ℂ) := by
    funext k; simp
  rw [h1, integral_complex_ofReal, Complex.ofReal_re]
  have h2 := integral_comp_abs (f := fun x : ℝ => Real.exp (-(x ^ α)))
  rw [h2, integral_exp_neg_rpow hα, Real.Gamma_add_one (by positivity)]
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp

end S74SP

open Arxivcond_mat_0408414 S74SP in
theorem solution (H s θ0 : ℝ) (hs : 0 < s) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hθ0 : θ0 ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    mdrcFinal H s θ0 θ0 =
      Real.Gamma (1 / (2 * H)) /
        (2 * √2 * π * H * (2 * √2 * π * cos θ0) ^ (1 / H - 1) * s ^ (1 / H)) := by
  have hc : 0 < cos θ0 := Real.cos_pos_of_mem_Ioo hθ0
  unfold mdrcFinal levyPrefactor levyArg
  have hA : levyA θ0 θ0 = 2 * √2 * π * cos θ0 := by
    unfold levyA; rw [sub_self, zero_div, Real.cos_zero]; ring_nf
  rw [hA, sub_self, zero_div, Real.cos_zero, Real.tan_zero, mul_zero, zero_div]
  have hL : levyDensity (2 * H) 0 = Real.Gamma (1 / (2 * H)) / ((2 * H) * π) := levy0 _ (by positivity)
  rw [hL, show (θ0 + θ0) / 2 = θ0 by ring]
  have hpos : 0 < 2 * √2 * π * cos θ0 := by positivity
  rw [Real.rpow_neg hpos.le, Real.rpow_neg hs.le]
  have : (0:ℝ) < (2 * √2 * π * cos θ0) ^ (1 / H - 1) := Real.rpow_pos_of_pos hpos _
  have : (0:ℝ) < s ^ (1 / H) := Real.rpow_pos_of_pos hs _
  have h2 : (0:ℝ) < √2 := by positivity
  field_simp
