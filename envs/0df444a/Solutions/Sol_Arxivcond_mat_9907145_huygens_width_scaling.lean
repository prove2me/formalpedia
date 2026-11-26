-- Prove2me | solution 1 for Arxivcond_mat_9907145.huygens_width_scaling
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T09:25:05.894801+00:00
-- url     : https://prove2.me/submissions/1bd3cae1-96b7-43cb-94c9-9051fc7918e0

import Mathlib
import Definitions.Def_Arxivcond_mat_9907145_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace HW
open Arxivcond_mat_9907145

lemma dR (lam r H : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    dRough lam (r * lam) H = lam * (r ^ (1 / H - 1))⁻¹ := by
  unfold dRough
  rw [mul_rpow hr.le hlam.le, ← rpow_neg hr.le]
  have : lam ^ (1 / H) * lam ^ (1 - 1 / H) = lam := by rw [← rpow_add hlam]; simp
  rw [show -(1 / H - 1) = 1 - 1 / H by ring]
  calc lam ^ (1 / H) * (r ^ (1 - 1 / H) * lam ^ (1 - 1 / H))
      = (lam ^ (1 / H) * lam ^ (1 - 1 / H)) * r ^ (1 - 1 / H) := by ring
    _ = _ := by rw [this]

end HW

open Arxivcond_mat_9907145 HW in
theorem solution (lam H θ0 : ℝ) (hlam : 0 < lam) (hH0 : 0 < H) (hH1 : H ≤ 1) :
    (∀ ell : ℝ, 0 < ell → incStd ell H (dRough lam ell H) = lam) ∧
    ∃ w : ℝ → ℝ,
      (∀ r : ℝ, 0 < r → 0 < w r ∧ w r < π ∧
        ∀ θ ∈ Set.Ioo θ0 (θ0 + π), dAng lam θ θ0 = dRough lam (r * lam) H ↔ θ = θ0 + w r) ∧
      ∃ C : ℝ, 0 < C ∧ Tendsto (fun r : ℝ => w r / r ^ (1 / H - 1)) (𝓝[>] 0) (𝓝 C) := by
  refine ⟨fun ell hell => ?_, fun r => 2 * arctan (r ^ (1 / H - 1)), fun r hr => ?_, ?_⟩
  · unfold incStd dRough
    rw [mul_rpow (by positivity) (by positivity), ← rpow_mul hlam.le, ← rpow_mul hell.le, mul_left_comm,
      ← rpow_add hell]
    rw [show 1 - H + (1 - 1 / H) * H = 0 by field_simp; ring, show 1 / H * H = 1 by field_simp]
    simp
  · have hy : 0 < r ^ (1 / H - 1) := by positivity
    refine ⟨by have := arctan_pos.mpr hy; linarith, by have := arctan_lt_pi_div_two (r ^ (1 / H - 1)); linarith,
      fun θ hθ => ?_⟩
    have hu1 : 0 < (θ - θ0) / 2 := by linarith [hθ.1]
    have hu2 : (θ - θ0) / 2 < π / 2 := by linarith [hθ.2]
    have ht : 0 < tan ((θ - θ0) / 2) := tan_pos_of_pos_of_lt_pi_div_two hu1 hu2
    unfold dAng
    rw [dR lam r H hlam hr]
    constructor
    · intro h
      have h' : tan ((θ - θ0) / 2) = r ^ (1 / H - 1) := by
        rw [div_eq_mul_inv] at h
        exact inv_inj.mp (mul_left_cancel₀ hlam.ne' h)
      have := congrArg arctan h'
      rw [arctan_tan (by linarith) hu2] at this
      linarith
    · intro h
      have : (θ - θ0) / 2 = arctan (r ^ (1 / H - 1)) := by rw [h]; ring
      rw [this, tan_arctan]
      field_simp
  · rcases hH1.lt_or_eq with hlt | heq
    · refine ⟨2, two_pos, ?_⟩
      have he : 0 < 1 / H - 1 := by rw [sub_pos, lt_div_iff₀ hH0]; linarith
      have hy : Tendsto (fun r : ℝ => r ^ (1 / H - 1)) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have := (Real.continuous_rpow_const he.le).tendsto 0
          rw [zero_rpow he.ne'] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact rpow_pos_of_pos hr _
      have hd := (hasDerivAt_arctan 0).tendsto_slope_zero_right
      simp only [zero_add, arctan_zero, sub_zero, smul_eq_mul] at hd
      have hd' : Tendsto (fun t : ℝ => arctan t / t) (𝓝[>] 0) (𝓝 1) := by
        convert hd using 2 with t
        · ring
        · norm_num
      have := (hd'.comp hy).const_mul 2
      simp only [mul_one] at this
      convert this using 2 with r
      simp [Function.comp]; ring
    · refine ⟨π / 2, by positivity, ?_⟩
      subst heq
      simp only [div_one, sub_self, rpow_zero, arctan_one]
      convert tendsto_const_nhds using 2; ring
