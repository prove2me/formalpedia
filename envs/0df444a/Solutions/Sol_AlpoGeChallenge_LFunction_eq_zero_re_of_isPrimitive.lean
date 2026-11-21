-- Prove2me | solution 1 for AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T23:53:55.794922+00:00
-- url     : https://prove2.me/submissions/980d6e9a-8b9d-46be-8bb0-fd28c62b8536
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_grh_critical_line_iff
import Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exp_zero_free_of_power_bound_only
import Theorems.Thm_OAI_ShortDraftMellin_principal_dirichlet_exp_zero_free_of_power_bound_only
import Theorems.Thm_GRH_smoothed_mobius_character_power_bound

open OAI.ShortDraftMellin

theorem solution :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 →
        s.re = 1 / 2 := by
  apply GRH.grh_critical_line_iff.mpr
  intro q _ χ s hs hpole
  obtain ⟨σ, hhalf, hmin⟩ :=
    exists_between (lt_min (by norm_num : (1 / 2 : ℝ) < 1) hs)
  have hone : σ < 1 := lt_of_lt_of_le hmin (min_le_left _ _)
  have hreal : σ < s.re := lt_of_lt_of_le hmin (min_le_right _ _)
  have hpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hbound := GRH.smoothed_mobius_character_power_bound q χ σ hhalf hone
  by_cases hχ : χ = 1
  · subst χ
    exact principal_dirichlet_exp_zero_free_of_power_bound_only q σ hpos hone
      hbound s hreal (fun heq => hpole ⟨rfl, heq⟩)
  · exact dirichlet_exp_zero_free_of_power_bound_only χ hχ σ hpos hone
      hbound s hreal
