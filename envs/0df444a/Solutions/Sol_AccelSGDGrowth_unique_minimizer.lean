-- Prove2me | solution 1 for AccelSGDGrowth.unique_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:59:23.707166+00:00
-- url     : https://prove2.me/submissions/1b5abb1c-c0f7-4370-8a84-f46d5221dcde

import Definitions.Def_AccelSGDGrowth_ClassF

open Filter Topology

open AccelSGDGrowth in
theorem solution {d : ℕ} {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ClassF m L f) :
    ∃! xstar : EuclideanSpace ℝ (Fin d), IsMinOn f Set.univ xstar := by
  obtain ⟨hC, hup, hlow⟩ := hf
  have hcont : Continuous f := hC.continuous
  have hbound : ∀ y, f 0 - ‖gradient f 0‖ * ‖y‖ + m / 2 * ‖y‖ ^ 2 ≤ f y := by
    intro y
    have h := hlow 0 y
    rw [sub_zero] at h
    have hcs : -(‖gradient f 0‖ * ‖y‖) ≤ inner ℝ (gradient f 0) y := by
      have := abs_real_inner_le_norm (gradient f 0) y
      rw [abs_le] at this
      linarith [this.1]
    linarith
  have hφ : Tendsto (fun r : ℝ => f 0 - ‖gradient f 0‖ * r + m / 2 * r ^ 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [eventually_ge_atTop (2 * (‖gradient f 0‖ + 1 + |f 0|) / m + 1)] with r hr
    have hg0 : 0 ≤ ‖gradient f 0‖ := norm_nonneg _
    have hf0 : -|f 0| ≤ f 0 := neg_abs_le _
    have hr1 : 1 ≤ r := by
      have : 0 ≤ 2 * (‖gradient f 0‖ + 1 + |f 0|) / m := div_nonneg (by positivity) hm.le
      linarith
    have hr2 : 2 * (‖gradient f 0‖ + 1 + |f 0|) ≤ m * r := by
      have h1 : 2 * (‖gradient f 0‖ + 1 + |f 0|) / m ≤ r := by linarith
      rw [div_le_iff₀ hm] at h1
      linarith
    simp only [id]
    have h3 := mul_le_mul_of_nonneg_right hr2 (by linarith : (0:ℝ) ≤ r)
    have h4 := mul_nonneg (abs_nonneg (f 0)) (by linarith : (0:ℝ) ≤ r - 1)
    have h5 := mul_nonneg hg0 (by linarith : (0:ℝ) ≤ r - 1)
    nlinarith
  have hcoer : Tendsto f (cocompact (EuclideanSpace ℝ (Fin d))) atTop :=
    tendsto_atTop_mono hbound (hφ.comp tendsto_norm_cocompact_atTop)
  obtain ⟨x, hx⟩ := hcont.exists_forall_le hcoer
  have hmin : ∀ z, IsMinOn f Set.univ z → gradient f z = 0 := by
    intro z hz
    have hloc : IsLocalMin f z := hz.isLocalMin Filter.univ_mem
    rw [gradient, hloc.fderiv_eq_zero, map_zero]
  refine ⟨x, fun y _ => hx y, fun y hy => ?_⟩
  have hgy := hmin y hy
  have h := hlow y x
  rw [hgy, inner_zero_left, add_zero] at h
  have hxy : f x ≤ f y := hx y
  have hyx : f y ≤ f x := hy (Set.mem_univ x)
  have hn : ‖x - y‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this.symm
