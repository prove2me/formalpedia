-- Prove2me | solution 1 for APFPaper5.K2.scoreNull_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:42:26.60768+00:00
-- url     : https://prove2.me/submissions/c22b2551-3940-47d3-9890-84916cdb84c4

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

theorem APFPaper5.K2.scoreNull_sandwich {ι : Type uI} [Fintype ι]
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ)
    {a' a b b' : Context} (coef : ι → ℝ) (w : ι → Word Frag a b)
    (L : Word Frag a' a) (R : Word Frag b b') (h : ScoreNull score coef w) :
    ScoreNull score coef (fun i => L.append ((w i).append R)) := by
  intro g c P S x
  have e : ∀ i, sandwich P (L.append ((w i).append R)) S = sandwich (P.append L) (w i) (R.append S) := by
    intro i
    simp only [sandwich, Word.append_assoc]
  simp only [e]
  exact h g c (P.append L) (R.append S) x

theorem solution {ι : Type uI} [Fintype ι]
    (score : (g : Context) → WordFrom Frag g → Raw g → ℝ)
    {a' a b b' : Context} (coef : ι → ℝ) (w : ι → Word Frag a b)
    (L : Word Frag a' a) (R : Word Frag b b') (h : ScoreNull score coef w) :
    ScoreNull score coef (fun i => L.append ((w i).append R)) := by
  intro g c P S x
  have e : ∀ i, sandwich P (L.append ((w i).append R)) S = sandwich (P.append L) (w i) (R.append S) := by
    intro i
    simp only [sandwich, Word.append_assoc]
  simp only [e]
  exact h g c (P.append L) (R.append S) x


