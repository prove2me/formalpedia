-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.continuous_zero_of_compact_smooth_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:22:07.163262+00:00
-- url     : https://prove2.me/submissions/3704384f-8a4b-4616-9943-590dc56bcf9a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped Topology
set_option autoImplicit false
theorem solution
    (g : ℝ -> ℝ) (hg : Continuous g)
    (htest : ∀ (φ : ℝ -> ℝ),
      ContDiff ℝ 2 φ -> HasCompactSupport φ ->
        (∫ x : ℝ, φ x * g x) = 0) :
    ∀ x : ℝ, g x = 0 := by
  intro x
  by_contra hx
  have hxpos : 0 < g x * g x := mul_self_pos.mpr hx
  have hOpen : IsOpen {z : ℝ | 0 < g x * g z} := by
    exact isOpen_Ioi.preimage (continuous_const.mul hg)
  obtain ⟨r, hr, hb⟩ :=
    Metric.isOpen_iff.mp hOpen x hxpos
  let β : ContDiffBump x :=
    ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hnonneg : ∀ z : ℝ, 0 <= β z * (g x * g z) := by
    intro z
    by_cases hz : z ∈ Metric.ball x r
    · exact mul_nonneg β.nonneg (le_of_lt (hb hz))
    · have hd : r <= dist z x := by
        simpa [Metric.mem_ball, not_lt] using hz
      have hzero : β z = 0 :=
        β.zero_of_le_dist (by change r <= dist z x; exact hd)
      simp [hzero]
  have hbcont : Continuous (fun z : ℝ => β z * (g x * g z)) :=
    β.continuous.mul (continuous_const.mul hg)
  have hbcomp : HasCompactSupport
      (fun z : ℝ => β z * (g x * g z)) := by
    exact β.hasCompactSupport.mul_right
  have hbetaOne : β x = 1 := by
    apply β.one_of_mem_closedBall
    have hR : 0 <= r / 2 := (half_pos hr).le
    simpa [Metric.mem_closedBall, β] using hR
  have hbpoint : β x * (g x * g x) ≠ 0 := by
    simpa [hbetaOne] using (ne_of_gt hxpos)
  have hintpos : 0 <
      ∫ z : ℝ, β z * (g x * g z) :=
    hbcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hbcomp hnonneg hbpoint
  have hzero : (∫ z : ℝ, β z * g z) = 0 :=
    htest β β.contDiff β.hasCompactSupport
  have heq : (fun z : ℝ => β z * (g x * g z)) =
      (fun z : ℝ => g x * (β z * g z)) := by
    funext z
    ring
  rw [heq, integral_const_mul, hzero] at hintpos
  norm_num at hintpos
