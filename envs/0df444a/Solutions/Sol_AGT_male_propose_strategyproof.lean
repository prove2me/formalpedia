-- Prove2me | solution 1 for AGT.male_propose_strategyproof
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T10:49:26.252776+00:00
-- url     : https://prove2.me/submissions/f1220ba0-12cf-4898-aa46-27607fabc73f

import Theorems.Thm_AGT_blocking_lemma

open AGT

/-- The male-propose mechanism is strategy-proof for the men, reduced to the
Blocking Lemma. -/
theorem solution {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M]
    (F : (M → W → W → Prop) → (W → M → M → Prop) → M ≃ W)
    (hF : ∀ PM PW, IsPrefProfile PM → IsPrefProfile PW →
      IsMaleOptimal PM PW (F PM PW)) :
    ∀ PM PW, IsPrefProfile PM → IsPrefProfile PW →
      ∀ m (r' : W → W → Prop), IsStrictTotalOrder W r' →
        F (Function.update PM m r') PW m = F PM PW m ∨
          PM m (F PM PW m) (F (Function.update PM m r') PW m) := by
  intro PM PW hM hW m r' hr'
  have hP' : IsPrefProfile (Function.update PM m r') := by
    intro i
    by_cases h : i = m
    · subst h; rwa [Function.update_self]
    · rw [Function.update_of_ne h]; exact hM i
  have hmu := hF PM PW hM hW
  have hnu := hF (Function.update PM m r') PW hP' hW
  set mu := F PM PW with hmudef
  set nu := F (Function.update PM m r') PW with hnudef
  have := hM m
  rcases trichotomous_of (PM m) (nu m) (mu m) with h | h | h
  · exfalso
    obtain ⟨m₁, m₂, _, h₁, hb1, hb2⟩ := blocking_lemma PM PW hM hW mu nu hmu m h
    have hne : m₁ ≠ m := by rintro rfl; exact h₁ h
    refine hnu.1 m₁ (nu m₂) ⟨?_, hb2⟩
    rwa [Function.update_of_ne hne]
  · exact Or.inl h
  · exact Or.inr h
