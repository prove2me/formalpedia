-- Prove2me | solution 1 for AffinePolicyOpt.OneDim.property_P3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:49:56.899191+00:00
-- url     : https://prove2.me/submissions/d061c415-c366-4145-9427-a418da34d0f0

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

set_option autoImplicit false

open AffinePolicyOpt.OneDim in
theorem a98f14cb_bounds (L U ystar : ℝ) (hLU : L ≤ U) (s t : ℝ) (hst : s ≤ t) :
    0 ≤ clampLaw L U ystar s - clampLaw L U ystar t ∧
      clampLaw L U ystar s - clampLaw L U ystar t ≤ t - s := by
  unfold clampLaw
  constructor <;>
  · simp only [max_def, min_def]
    split_ifs <;> linarith

open AffinePolicyOpt.OneDim in
theorem solution (L U ystar : ℝ) (hLU : L ≤ U) (s t : ℝ) (hst : s ≤ t) :
    ∃ f ∈ Set.Icc (0 : ℝ) 1,
      clampLaw L U ystar s - clampLaw L U ystar t = -f * (s - t) := by
  obtain ⟨h0, h1⟩ := a98f14cb_bounds L U ystar hLU s t hst
  rcases eq_or_lt_of_le hst with h | h
  · subst h
    refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
    simp
  · have hpos : 0 < t - s := sub_pos.mpr h
    refine ⟨(clampLaw L U ystar s - clampLaw L U ystar t) / (t - s), ⟨div_nonneg h0 hpos.le, ?_⟩, ?_⟩
    · rw [div_le_one hpos]; exact h1
    · field_simp
      ring
