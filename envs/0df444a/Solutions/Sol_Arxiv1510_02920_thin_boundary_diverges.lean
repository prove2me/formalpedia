-- Prove2me | solution 1 for Arxiv1510_02920.thin_boundary_diverges
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:54:56.497704+00:00
-- url     : https://prove2.me/submissions/d5918725-702e-4381-8879-33228e83bceb

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

lemma tb_tanh_deriv (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun y : ℝ => Real.tanh (-y / a)) (-1 / a) 0 := by
  have hin : HasDerivAt (fun y : ℝ => -y / a) (-1 / a) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).neg).div_const a
  have hs := (Real.hasDerivAt_sinh (-(0:ℝ) / a)).comp (0:ℝ) hin
  have hc := (Real.hasDerivAt_cosh (-(0:ℝ) / a)).comp (0:ℝ) hin
  have hq := hs.div hc (Real.cosh_pos _).ne'
  have e : (fun y : ℝ => Real.tanh (-y / a)) = fun y => Real.sinh (-y / a) / Real.cosh (-y / a) := by
    funext y; rw [Real.tanh_eq_sinh_div_cosh]
  rw [e]
  exact hq.congr_deriv (by simp)

lemma tb_P_deriv (Om a γ : ℝ) (ha : 0 < a) (ω : ℂ) :
    HasDerivAt (fun y : ℝ => tanhP Om a γ y ω)
      (((Om ^ 2 / 2 * (-1 / a) : ℝ) : ℂ) / ((γ : ℂ) - Complex.I * ω) ^ 2) 0 := by
  have hr : HasDerivAt (fun y : ℝ => Om ^ 2 / 2 * (1 + Real.tanh (-y / a))) (Om ^ 2 / 2 * (-1 / a)) 0 := by
    simpa using ((tb_tanh_deriv a ha).const_add 1).const_mul (Om ^ 2 / 2)
  have hc := (hr.ofReal_comp).div_const (((γ : ℂ) - Complex.I * ω) ^ 2)
  have := hc.const_add 1
  unfold tanhP ansatzP tanhProfile
  exact this

theorem thin_boundary_diverges (c γ Om ω : ℝ) (hc : 0 < c) (hγ : 0 < γ) (hOm : Om ≠ 0)
    (hω : ω ≠ 0) :
    Tendsto (fun a : ℝ => ‖tanhPerm c Om a γ 0 (ω : ℂ)‖) (𝓝[>] 0) atTop := by
  set Z : ℂ := ((γ : ℂ) - Complex.I * ω) ^ 2 with hZ
  have hZ0 : Z ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  set P0 : ℂ := 1 + ((Om ^ 2 / 2 : ℝ) : ℂ) / Z with hP0
  set K : ℝ := c / |ω| * (Om ^ 2 / 2) / ‖Z‖ with hK
  have hKpos : 0 < K := by
    have : 0 < ‖Z‖ := norm_pos_iff.mpr hZ0
    have : 0 < |ω| := abs_pos.mpr hω
    have : 0 < Om ^ 2 := by positivity
    positivity
  have hval : ∀ a : ℝ, 0 < a → tanhPerm c Om a γ 0 (ω : ℂ) =
      P0 ^ 2 - Complex.I * (c : ℂ) / (ω : ℂ) *
        (((Om ^ 2 / 2 * (-1 / a) : ℝ) : ℂ) / Z) := by
    intro a ha
    unfold tanhPerm perm
    rw [(tb_P_deriv Om a γ ha (ω : ℂ)).deriv]
    congr 2
    unfold tanhP ansatzP tanhProfile
    simp [hP0, hZ]
  have hlow : ∀ a : ℝ, 0 < a → K * a⁻¹ - ‖P0 ^ 2‖ ≤ ‖tanhPerm c Om a γ 0 (ω : ℂ)‖ := by
    intro a ha
    rw [hval a ha, norm_sub_rev]
    have hn : ‖Complex.I * (c : ℂ) / (ω : ℂ) * (((Om ^ 2 / 2 * (-1 / a) : ℝ) : ℂ) / Z)‖ = K * a⁻¹ := by
      rw [norm_mul, norm_div, norm_mul, norm_div, Complex.norm_I, Complex.norm_real,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hc, hK]
      have : |Om ^ 2 / 2 * (-1 / a)| = Om ^ 2 / 2 * a⁻¹ := by
        rw [abs_mul, abs_of_nonneg (by positivity), abs_div, abs_neg, abs_one, abs_of_pos ha]; ring
      rw [this]; ring
    have := norm_sub_norm_le (Complex.I * (c : ℂ) / (ω : ℂ) * (((Om ^ 2 / 2 * (-1 / a) : ℝ) : ℂ) / Z)) (P0 ^ 2)
    linarith
  have hinf : Tendsto (fun a : ℝ => K * a⁻¹ - ‖P0 ^ 2‖) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_inv_nhdsGT_zero.const_mul_atTop hKpos)
  refine tendsto_atTop_mono' _ ?_ hinf
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact hlow a ha

end Arxiv1510_02920
open Arxiv1510_02920 in
theorem solution (c γ Om ω : ℝ) (hc : 0 < c) (hγ : 0 < γ) (hOm : Om ≠ 0)
    (hω : ω ≠ 0) :
    Tendsto (fun a : ℝ => ‖tanhPerm c Om a γ 0 (ω : ℂ)‖) (𝓝[>] 0) atTop :=
  thin_boundary_diverges c γ Om ω hc hγ hOm hω
