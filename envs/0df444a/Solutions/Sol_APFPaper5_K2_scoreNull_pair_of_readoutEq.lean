-- Prove2me | solution 1 for APFPaper5.K2.scoreNull_pair_of_readoutEq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:42:34.751427+00:00
-- url     : https://prove2.me/submissions/1b33e8cb-1bb4-46a0-8f44-5df231b4abb0

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

theorem APFPaper5.K2.scoreNull_pair_of_readoutEq (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ) (hz : ZeroConvention Defd score)
    {a b : Context} (W W' : Word Frag a b) (h : ReadoutEq Defd score W W') :
    ScoreNull score (fun i : Bool => if i then (1 : ℝ) else -1) (fun i : Bool => if i then W else W') := by
  intro g c P S x
  obtain ⟨h1, h2⟩ := h g c P S x trivial trivial
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  by_cases hd : Defd g x (sandwich P W S)
  · rw [h2 hd (h1.mp hd)]; simp
  · rw [hz _ _ _ hd, hz _ _ _ (fun h' => hd (h1.mpr h'))]; simp

theorem solution (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ) (hz : ZeroConvention Defd score)
    {a b : Context} (W W' : Word Frag a b) (h : ReadoutEq Defd score W W') :
    ScoreNull score (fun i : Bool => if i then (1 : ℝ) else -1) (fun i : Bool => if i then W else W') := by
  intro g c P S x
  obtain ⟨h1, h2⟩ := h g c P S x trivial trivial
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  by_cases hd : Defd g x (sandwich P W S)
  · rw [h2 hd (h1.mp hd)]; simp
  · rw [hz _ _ _ hd, hz _ _ _ (fun h' => hd (h1.mpr h'))]; simp


