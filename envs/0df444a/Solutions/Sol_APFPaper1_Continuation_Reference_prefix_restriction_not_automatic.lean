-- Prove2me | solution 1 for APFPaper1.Continuation.Reference.prefix_restriction_not_automatic
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:20:03.057491+00:00
-- url     : https://prove2.me/submissions/46414045-6575-4cfd-9678-bb0a644510c3

import Definitions.Def_APFPaper1_Cont_prefix_countermodel_data
/-
REFERENCE ONLY. Not a Foundation Ledger node (standing rule 11: countermodels stay in reference missions).
DRAFT, not gated, not released.
name: APFPaper1.Continuation.Reference.prefix_restriction_not_automatic
purpose: shows that the bill-comparison hypothesis of C3 (Thm_APFPaper1_Cont_prefix_restriction) cannot be dropped.
model: one context; one fragment; every step allowed; the resource of a word is its length; the calibration
  charges 2 for a word of length one and 0 otherwise; capacity 1. The two-fragment word executes and has bill
  0, so it is in Cont. Its one-fragment initial segment has bill 2 > 1, so it is not. The same model shows the
  whole-word class and the hereditary class differ, and that Cont is inhabited.
what it does not show: nothing about physical resources. The calibration here is not monotone in any physical
  sense; the model only separates the two definitions.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation.Reference
open APFPaper1.Continuation













theorem one_isPrefix_two : IsPrefix one two :=
  ⟨Word.single (g := ()) (h := ()) (), rfl⟩

theorem two_executes : Executes step two.2 () () := by
  show ∃ y : Unit, step () () () () y ∧ ∃ y' : Unit, step () () () y y' ∧ y' = ()
  exact ⟨(), trivial, (), trivial, rfl⟩

theorem prefix_restriction_not_automatic :
    IsPrefix one two ∧
      Cont step resource calibration capacity () () two ∧
      ¬ Cont step resource calibration capacity () () one := by
  refine ⟨one_isPrefix_two, ⟨⟨(), two_executes⟩, ?_⟩, ?_⟩
  · show calibration () (resource () two) ≤ capacity ()
    simp [calibration, resource, two, length, capacity, Word.single]
  · intro h
    have h2 : (2 : NNReal) ≤ 1 := by
      simpa [calibration, resource, one, length, capacity, Word.single] using h.2
    exact absurd h2 (not_le.mpr one_lt_two)

end APFPaper1.Continuation.Reference


theorem solution :
APFPaper1.Continuation.IsPrefix.{0, 0} APFPaper1.Continuation.Reference.one APFPaper1.Continuation.Reference.two ∧
  APFPaper1.Continuation.Cont.{0, 0, 0, 0} APFPaper1.Continuation.Reference.step
      APFPaper1.Continuation.Reference.resource APFPaper1.Continuation.Reference.calibration
      APFPaper1.Continuation.Reference.capacity () () APFPaper1.Continuation.Reference.two ∧
    ¬APFPaper1.Continuation.Cont.{0, 0, 0, 0} APFPaper1.Continuation.Reference.step
        APFPaper1.Continuation.Reference.resource APFPaper1.Continuation.Reference.calibration
        APFPaper1.Continuation.Reference.capacity () () APFPaper1.Continuation.Reference.one := by
  exact @APFPaper1.Continuation.Reference.prefix_restriction_not_automatic
