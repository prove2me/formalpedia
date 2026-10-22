-- Prove2me | solution 1 for AdDataSharing.Base.revenue_bound_open
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:41:28.336761+00:00
-- url     : https://prove2.me/submissions/480a3553-01c4-40d5-bcd8-cb2ef556b57e

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model
set_option autoImplicit false

open AdDataSharing.Base

theorem solution (P : Params) (hP : P.Standing) :
    (∀ σ : Plan × Plan, ¬ (σ.1.ex = .adx1 ∧ σ.2.ex = .adx1) →
        revenue P true σ ≤ 2 * P.w * P.φ * (1 - P.α + P.η₁)) ∧
      (∀ s : Bool, revenue P true (⟨.adx1, s⟩, ⟨.adx2, true⟩) = 2 * P.w * P.φ * (1 - P.α + P.η₁)) ∧
      2 * P.w * P.φ * (1 - P.α + P.η₁) < 2 * P.w * P.φ * (1 - P.α + P.η₂) := by
  obtain ⟨hα0, hα1, hw, -, -, -, hφ0, -, hη1, hη12⟩ := hP
  have hwφ : 0 < P.w * P.φ := mul_pos hw hφ0
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨e1, s1⟩, ⟨e2, s2⟩⟩ h
    have key : 0 < P.w * P.φ * (1 - P.α) := mul_pos hwφ (by linarith)
    have key2 : 0 < P.w * P.φ * P.η₁ := mul_pos hwφ hη1
    cases e1 <;> cases e2 <;> cases s1 <;> cases s2 <;>
      simp at h <;> simp [revenue, adsOnADX1] <;> nlinarith [key, key2]
  · intro s
    simp [revenue, adsOnADX1]; ring
  · have : 0 < P.w * P.φ * (P.η₂ - P.η₁) := mul_pos hwφ (by linarith)
    nlinarith
