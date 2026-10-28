-- Prove2me | solution 1 for AdDataSharing.Base.revenue_closed
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:38:57.590988+00:00
-- url     : https://prove2.me/submissions/e0246a1e-bfe5-4a14-8362-4ef7f3b7f04a

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace Aux_AdDataSharing_revenue_closed
open AdDataSharing.Base

theorem spe_closed (P : Params) (hP : P.Standing) (σ : Plan × Plan) (hσ : IsSPE P false σ) :
    σ.1.ex = .adx1 ∧ σ.2.ex = .adx1 := by
  obtain ⟨hα0, hα1, hw, hwC, hCM, hM, hφ0, hφ1, hη1, hη2⟩ := hP
  have hCw : 0 < P.C - P.w := by linarith
  have k1 : 0 < (P.η₂ - P.η₁) * (P.C - P.w) := mul_pos (by linarith) hCw
  have k2 : 0 < P.η₁ * (P.C - P.w) := mul_pos hη1 hCw
  rcases σ with ⟨⟨e1, s1⟩, ⟨e2, s2⟩⟩
  obtain ⟨-, h1, h2⟩ := hσ
  have a1 := h1 .adx1
  have a2 := h2 .adx1
  cases e1 <;> cases e2
  · exact ⟨rfl, rfl⟩
  all_goals exfalso
  all_goals simp only [payoff, payoffClosed, lookAlike, Bool.false_eq_true, ↓reduceIte] at a1 a2
  all_goals nlinarith

end Aux_AdDataSharing_revenue_closed

open AdDataSharing.Base in
theorem solution (P : Params) (hP : P.Standing) (σ : Plan × Plan) (hσ : IsSPE P false σ) :
    revenue P false σ = 2 * P.w * P.φ * (1 - P.α + P.η₂) := by
  have h := Aux_AdDataSharing_revenue_closed.spe_closed P hP σ hσ
  rcases σ with ⟨⟨e1, s1⟩, ⟨e2, s2⟩⟩
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  subst h1 h2
  simp only [revenue, adsOnADX1, Bool.false_eq_true, ↓reduceIte]
  ring
