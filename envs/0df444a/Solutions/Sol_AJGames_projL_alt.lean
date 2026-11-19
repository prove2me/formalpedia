-- Prove2me | solution 1 for AJGames.projL_alt
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:40:57.318826+00:00
-- url     : https://prove2.me/submissions/3d597be0-ed47-46d2-b6fd-e1cd39547e5e

import Mathlib
import Definitions.Def_AJGames_Game
import Definitions.Def_AJGames_Tensor

set_option autoImplicit false
universe u

namespace PLAux
open AJGames


lemma ne_O {p : Pl} (h : p ≠ Pl.O) : p = Pl.P := by cases p <;> simp_all

lemma key {α β : Type u} (la : α → Pl) (lb : β → Pl) :
    ∀ s : List (α ⊕ β), List.IsChain (TR la lb) s →
      Alt la (projL s) ∧
      (∀ b rest, s = Sum.inr b :: rest → ∀ a' ∈ (projL s).head?, la a' = Pl.O) := by
  intro s
  induction s with
  | nil =>
    intro _
    refine ⟨?_, ?_⟩
    · simp [projL, Alt]
    · intro b rest h; cases h
  | cons x rest ih =>
    intro h
    obtain ⟨ih1, ih2⟩ := ih h.tail
    cases x with
    | inl a =>
      refine ⟨?_, ?_⟩
      · have hp : projL (Sum.inl a :: rest) = a :: projL rest := by
          simp [projL]
        rw [hp, Alt, List.isChain_cons]
        refine ⟨?_, ih1⟩
        intro a'' ha''
        rcases rest with _ | ⟨y, rest'⟩
        · simp [projL] at ha''
        · have hT : TR la lb (Sum.inl a) y := (List.isChain_cons_cons.1 h).1
          cases y with
          | inl a2 =>
            have : a'' = a2 := by simpa [projL] using ha''.symm
            subst this
            simpa [TR] using hT.1
          | inr b =>
            have hO := ih2 b rest' rfl a'' ha''
            have hb : lb b = Pl.O := by
              rcases hT.2 with h2 | h2
              · simp at h2
              · simpa using h2
            have h1 : la a ≠ lb b := by simpa using hT.1
            rw [hO]; rw [hb] at h1; exact h1
      · intro b r hr; cases hr
    | inr b =>
      have hp : projL (Sum.inr b :: rest) = projL rest := by unfold projL; rfl
      refine ⟨by rw [hp]; exact ih1, ?_⟩
      intro b' r hr a' ha'
      rw [hp] at ha'
      rcases rest with _ | ⟨y, rest'⟩
      · simp [projL] at ha'
      · have hT : TR la lb (Sum.inr b) y := (List.isChain_cons_cons.1 h).1
        cases y with
        | inl a2 =>
          have : a' = a2 := by simpa [projL] using ha'.symm
          subst this
          rcases hT.2 with h2 | h2
          · simp at h2
          · simpa using h2
        | inr b2 => exact ih2 b2 rest' rfl a' ha'

end PLAux

open AJGames in
theorem solution {α β : Type u} (la : α → Pl) (lb : β → Pl) :
    ∀ s : List (α ⊕ β), List.IsChain (TR la lb) s → Alt la (projL s) :=
  fun s h => (PLAux.key la lb s h).1
