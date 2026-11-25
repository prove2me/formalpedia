-- Prove2me | solution 1 for Arxiv2105_07250.collinear_receivers_same_frequency
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:42:04.550419+00:00
-- url     : https://prove2.me/submissions/237c6dfb-d458-499a-95bf-405ab808d5e1

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory Filter Topology

open Arxiv2105_07250 in
theorem solution (c : ℝ) (hc : 0 < c) (v : Plane) (hv0 : v ≠ 0)
    (hv : ‖v‖ < c) (wt : ℝ) (xA xB : Plane)
    (hside : 0 < (v 0 * xA 1 - v 1 * xA 0) * (v 0 * xB 1 - v 1 * xB 0)) (t' : ℝ)
    (hcol : ∃ l : ℝ, xB - t' • v = l • (xA - t' • v)) :
    cosTheta xA v t' = cosTheta xB v t' ∧
      recordedFrequency c wt xA v t' = recordedFrequency c wt xB v t' := by
  obtain ⟨l, hl⟩ := hcol
  have h0 := congrFun (congrArg (⇑) hl) 0
  have h1 := congrFun (congrArg (⇑) hl) 1
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
  have hcr : v 0 * xB 1 - v 1 * xB 0 = l * (v 0 * xA 1 - v 1 * xA 0) := by
    have e0 : xB 0 = l * (xA 0 - t' * v 0) + t' * v 0 := by linarith
    have e1 : xB 1 = l * (xA 1 - t' * v 1) + t' * v 1 := by linarith
    rw [e0, e1]; ring
  rw [hcr] at hside
  have hlpos : 0 < l := by
    by_contra h; push Not at h
    nlinarith [sq_nonneg (v 0 * xA 1 - v 1 * xA 0)]
  have hcos : cosTheta xA v t' = cosTheta xB v t' := by
    unfold cosTheta
    rw [hl, inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos hlpos]
    simp only [conj_trivial]
    by_cases hz : ‖xA - t' • v‖ * ‖v‖ = 0
    · rw [mul_assoc, hz]; simp [hz]
    · field_simp
  exact ⟨hcos, by unfold recordedFrequency; rw [hcos]⟩
