-- Prove2me | solution 1 for APFPaper5.K2.readoutEq_iff_admissionScore_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:42:27.715711+00:00
-- url     : https://prove2.me/submissions/80132bbb-6d52-445c-ab65-c01322735dbf

import Definitions.Def_APFPaper5_K2_closed_boundary_on_words_Vocabulary
import Definitions.Def_APFPaper5_K2_ClosedBoundary
import Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich
import Theorems.Thm_APFPaper1_Continuation_contextEq_sandwich_all
import Theorems.Thm_APFPaper1_Continuation_contextEq_all_of_ambientHeredity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

set_option autoImplicit false
open APFPaper1.Continuation

namespace APFPaper5.K2
end APFPaper5.K2
open APFPaper5
open APFPaper5.K2
universe uC uF uX uV uR uI
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {Val : Type uV}

/-! ### The classes multiply -/



















/-! ### The word admitted nowhere is the zero -/













/-! ### Words that differ are told apart by a completed word -/











/-! ### The combinations no score can see -/







/-! ### The admission score -/

theorem APFPaper5.K2.readoutEq_iff_admissionScore_eq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    {a b : Context} (W W' : Word Frag a b) :
    ReadoutEq Defd (fun (_ : Context) (_ : WordFrom Frag _) (_ : Raw _) => ()) W W' ↔
      ∀ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
        admissionScore Defd g (sandwich P W S) x = admissionScore Defd g (sandwich P W' S) x := by
  constructor
  · intro h g c P S x
    obtain ⟨h1, -⟩ := h g c P S x trivial trivial
    unfold admissionScore
    by_cases hd : Defd g x (sandwich P W S)
    · simp [hd, h1.mp hd]
    · have hd' : ¬ Defd g x (sandwich P W' S) := fun h' => hd (h1.mpr h')
      simp [hd, hd']
  · intro h g c P S x _ _
    refine ⟨?_, fun _ _ => rfl⟩
    have := h g c P S x
    unfold admissionScore at this
    by_cases hd : Defd g x (sandwich P W S) <;> by_cases hd' : Defd g x (sandwich P W' S) <;>
      simp [hd, hd'] at this ⊢

theorem solution (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    {a b : Context} (W W' : Word Frag a b) :
    ReadoutEq Defd (fun (_ : Context) (_ : WordFrom Frag _) (_ : Raw _) => ()) W W' ↔
      ∀ (g c : Context) (P : Word Frag g a) (S : Word Frag b c) (x : Raw g),
        admissionScore Defd g (sandwich P W S) x = admissionScore Defd g (sandwich P W' S) x := by
  constructor
  · intro h g c P S x
    obtain ⟨h1, -⟩ := h g c P S x trivial trivial
    unfold admissionScore
    by_cases hd : Defd g x (sandwich P W S)
    · simp [hd, h1.mp hd]
    · have hd' : ¬ Defd g x (sandwich P W' S) := fun h' => hd (h1.mpr h')
      simp [hd, hd']
  · intro h g c P S x _ _
    refine ⟨?_, fun _ _ => rfl⟩
    have := h g c P S x
    unfold admissionScore at this
    by_cases hd : Defd g x (sandwich P W S) <;> by_cases hd' : Defd g x (sandwich P W' S) <;>
      simp [hd, hd'] at this ⊢


