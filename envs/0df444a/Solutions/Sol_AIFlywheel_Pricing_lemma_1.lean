-- Prove2me | solution 1 for AIFlywheel.Pricing.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T04:09:03.896076+00:00
-- url     : https://prove2.me/submissions/9a46d25e-8b09-4d50-b6ad-5ecccfd09257

import Mathlib
import Definitions.Def_AIFlywheel_Pricing_Model

open AIFlywheel.Pricing

theorem solution (ν α : ℝ) (hν : 0 < ν) (hα : 0 < α) :
    deltaM ν ∈ Set.Icc 0 ν ∧
    (∀ δ ∈ Set.Icc 0 ν, revenue ν δ α ≤ revenue ν (deltaM ν) α) ∧
    (∀ δ ∈ Set.Icc 0 ν, revenue ν δ α = revenue ν (deltaM ν) α →
      δ = deltaM ν) ∧
    J2b ν α = α * tau := by
  have hdM : deltaM ν = ν / 2 := by unfold deltaM phiInvZero; ring
  have hrev : ∀ δ, revenue ν δ α = α * (δ / ν) * (1 - δ / ν) := by
    intro δ; simp [revenue, uniformQuantile]
  have hval : revenue ν (deltaM ν) α = α / 4 := by
    rw [hrev, hdM]; field_simp; ring
  have hle : ∀ δ ∈ Set.Icc 0 ν, revenue ν δ α ≤ revenue ν (deltaM ν) α := by
    intro δ _
    rw [hval, hrev]
    have h1 : (δ / ν) * (1 - δ / ν) ≤ 1 / 4 := by nlinarith [sq_nonneg (δ / ν - 1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hα.le]
  have htau : tau = 1 / 4 := by unfold tau phiInvZero; norm_num
  refine ⟨?_, hle, ?_, ?_⟩
  · rw [hdM]; exact ⟨by linarith, by linarith⟩
  · intro δ _ heq
    rw [hval, hrev] at heq
    have h2 : α * (δ / ν - 1 / 2) ^ 2 = 0 := by nlinarith
    have h3 : (δ / ν - 1 / 2) ^ 2 = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h hα.ne'
      · exact h
    have h4 : δ / ν = 1 / 2 := by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h3]
    rw [hdM]
    field_simp at h4
    linarith
  · unfold J2b
    rw [htau]
    apply IsGreatest.csSup_eq
    refine ⟨⟨deltaM ν, ⟨by rw [hdM]; linarith, by rw [hdM]; linarith⟩, ?_⟩, ?_⟩
    · dsimp only; rw [hval]; ring
    · rintro _ ⟨δ, hδ, rfl⟩
      dsimp only
      have := hle δ hδ
      rw [hval] at this
      linarith
