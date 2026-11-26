-- Prove2me | solution 1 for Arxiv1811_00800.eq6_cone_dip_iff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:38:58.671382+00:00
-- url     : https://prove2.me/submissions/6680f5ab-e7ba-4fdb-a528-b6bb0e718df5

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Complex

namespace S73CD
open Arxiv1811_00800

lemma key (beta : NNReal) (a : ℝ) : poissonEnhancement beta a =
    1 + Real.exp ((beta : ℝ) * (Real.cos (4 * Real.pi * a) - 1)) *
      Real.cos ((beta : ℝ) * Real.sin (4 * Real.pi * a)) := by
  unfold poissonEnhancement
  rw [Complex.exp_re]
  congr 3
  · simp [Complex.mul_re]
    left; have h := Complex.exp_ofReal_mul_I_re (4 * Real.pi * a); push_cast at h; exact h
  · simp [Complex.mul_im]
    left; have h := Complex.exp_ofReal_mul_I_im (4 * Real.pi * a); push_cast at h; exact h

end S73CD

open Arxiv1811_00800 S73CD in
theorem solution (beta : NNReal) :
    (∃ alpha ∈ Set.Ioo (0 : ℝ) (1 / 2), poissonEnhancement beta alpha < 1) ↔
      Real.pi / 2 < (beta : ℝ) := by
  have hb0 : (0:ℝ) ≤ beta := beta.2
  constructor
  · rintro ⟨a, -, ha⟩
    by_contra hb
    push Not at hb
    rw [key] at ha
    have hc : 0 ≤ Real.cos ((beta : ℝ) * Real.sin (4 * Real.pi * a)) := by
      apply Real.cos_nonneg_of_mem_Icc
      have h1 := Real.sin_le_one (4 * Real.pi * a)
      have h2 := Real.neg_one_le_sin (4 * Real.pi * a)
      constructor <;> nlinarith
    have := Real.exp_pos ((beta : ℝ) * (Real.cos (4 * Real.pi * a) - 1))
    nlinarith
  · intro hb
    set t : ℝ := (Real.pi / 2 + min (beta:ℝ) Real.pi) / 2 with ht
    have hm1 : Real.pi / 2 < min (beta:ℝ) Real.pi := lt_min hb (by linarith [Real.pi_pos])
    have hm2 : min (beta:ℝ) Real.pi ≤ beta := min_le_left _ _
    have hm3 : min (beta:ℝ) Real.pi ≤ Real.pi := min_le_right _ _
    have ht1 : Real.pi / 2 < t := by rw [ht]; linarith
    have ht2 : t < beta := by rw [ht]; linarith
    have ht3 : t < Real.pi := by rw [ht]; linarith
    have hbpos : (0:ℝ) < beta := by linarith [Real.pi_pos]
    set s : ℝ := t / beta with hs
    have hs0 : 0 < s := div_pos (by linarith [Real.pi_pos]) hbpos
    have hs1 : s < 1 := (div_lt_one hbpos).2 ht2
    set θ := Real.arcsin s with hθ
    have hθ0 : 0 < θ := Real.arcsin_pos.2 hs0
    have hθ1 : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two s
    have hsin : Real.sin θ = s := Real.sin_arcsin (by linarith) hs1.le
    refine ⟨θ / (4 * Real.pi), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
    · rw [key]
      have e : 4 * Real.pi * (θ / (4 * Real.pi)) = θ := by field_simp
      rw [e, hsin]
      have e2 : (beta:ℝ) * s = t := by rw [hs]; field_simp
      rw [e2]
      have hc : Real.cos t < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt ht1 (by linarith [Real.pi_pos])
      have := Real.exp_pos ((beta : ℝ) * (Real.cos θ - 1))
      nlinarith
