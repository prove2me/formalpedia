-- Prove2me | solution 1 for AdDataSharing.Base.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:36:43.375997+00:00
-- url     : https://prove2.me/submissions/6023df89-5b59-4966-9b52-19ff8d18659a

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

open AdDataSharing.Base in
theorem solution (P : Params) (hP : P.Standing) (σ : Plan × Plan) :
    IsSPE P false σ ↔ σ.1.ex = .adx1 ∧ σ.2.ex = .adx1 := by
  obtain ⟨hα0, hα1, hw, hwC, hCM, hM, hφ0, hφ1, hη1, hη2⟩ := hP
  have hCw : 0 < P.C - P.w := by linarith
  have k1 : 0 < (P.η₂ - P.η₁) * (P.C - P.w) := mul_pos (by linarith) hCw
  have k2 : 0 < P.η₁ * (P.C - P.w) := mul_pos hη1 hCw
  rcases σ with ⟨⟨e1, s1⟩, ⟨e2, s2⟩⟩
  constructor
  · rintro ⟨-, h1, h2⟩
    have a1 := h1 .adx1
    have a2 := h2 .adx1
    cases e1 <;> cases e2
    · exact ⟨rfl, rfl⟩
    all_goals exfalso
    all_goals simp only [payoff, payoffClosed, lookAlike, Bool.false_eq_true, ↓reduceIte] at a1 a2
    all_goals nlinarith
  · rintro ⟨h1, h2⟩
    simp only at h1 h2
    subst h1 h2
    refine ⟨fun h => absurd h Bool.false_ne_true, ?_, ?_⟩
    all_goals intro e
    all_goals cases e
    all_goals (try simp only [payoff, payoffClosed, lookAlike, Bool.false_eq_true, ↓reduceIte])
    all_goals nlinarith
