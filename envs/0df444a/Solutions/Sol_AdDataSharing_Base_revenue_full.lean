-- Prove2me | solution 1 for AdDataSharing.Base.revenue_full
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:21:09.699146+00:00
-- url     : https://prove2.me/submissions/eb32883f-30b8-4365-9190-bb4ffa7a6ec3

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

open AdDataSharing.Base in
theorem solution (P : Params) (hP : P.Standing) :
    (∀ σ : Plan × Plan, σ.1.ex = .adx1 → σ.2.ex = .adx1 →
        revenue P true σ = 2 * P.w * P.φ * (1 + P.η₂)) ∧
      2 * P.w * P.φ * (1 - P.α + P.η₂) < 2 * P.w * P.φ * (1 + P.η₂) := by
  obtain ⟨hα0, hα1, hw, hwC, hCM, hM, hφ0, hφ1, hη1, hη2⟩ := hP
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨e1, s1⟩, ⟨e2, s2⟩⟩ h1 h2
    simp only at h1 h2
    subst h1 h2
    simp only [revenue, adsOnADX1, if_true]
    ring
  · have : 0 < P.w * P.φ * P.α := mul_pos (mul_pos hw hφ0) hα0
    nlinarith
