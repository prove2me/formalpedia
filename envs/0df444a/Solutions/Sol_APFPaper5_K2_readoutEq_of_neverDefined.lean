-- Prove2me | solution 1 for APFPaper5.K2.readoutEq_of_neverDefined
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:42:25.502119+00:00
-- url     : https://prove2.me/submissions/fed99766-05d8-4551-8d07-79370cd976e0

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

theorem APFPaper5.K2.readoutEq_of_neverDefined (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b)
    (h : NeverDefined Defd W) (h' : NeverDefined Defd W') : ReadoutEq Defd value W W' := by
  intro g c P S x _ _
  exact ⟨iff_of_false (h g c P S x) (h' g c P S x), fun hd => absurd hd (h g c P S x)⟩

theorem solution (Defd : (g : Context) → Raw g → WordFrom Frag g → Prop)
    (value : (g : Context) → WordFrom Frag g → Raw g → Val)
    {a b : Context} (W W' : Word Frag a b)
    (h : NeverDefined Defd W) (h' : NeverDefined Defd W') : ReadoutEq Defd value W W' := by
  intro g c P S x _ _
  exact ⟨iff_of_false (h g c P S x) (h' g c P S x), fun hd => absurd hd (h g c P S x)⟩


