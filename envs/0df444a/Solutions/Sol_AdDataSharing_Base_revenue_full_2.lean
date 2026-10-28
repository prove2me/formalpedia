-- Prove2me | solution 2 for AdDataSharing.Base.revenue_full
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:22:01.843916+00:00
-- url     : https://prove2.me/submissions/bc19e5a4-7adb-48c3-a220-3452ef489548

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
    norm_num [revenue, adsOnADX1] <;> ring
  · have : 0 < P.w * P.φ * P.α := mul_pos (mul_pos hw hφ0) hα0
    nlinarith
