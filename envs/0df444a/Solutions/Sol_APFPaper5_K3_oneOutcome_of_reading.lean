-- Prove2me | solution 1 for APFPaper5.K3.oneOutcome_of_reading
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:46:33.767968+00:00
-- url     : https://prove2.me/submissions/2e284982-21fe-4c77-97ea-3275268a41d3

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K3_undone_of_reading
title: A move that re-reads the place one to one, with admission that does not depend on the reading, can be taken again where it lands, and on finitely many places is undone
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's "Proceed" of 2026-11-14 17:01 HST (see Def_APFPaper5_K3_ReadingInvariance).
 Thm_APFPaper5_K3_undone_where_it_lands (pass 50: the three conditions). FOUNDATION_INPUTS is not consumed.
consumes_inputs: none. Plain mathematics about a relation on a set of places.
statement: (goesOn_of_reading) if the move is a re-reading and admission does not depend on that reading,
 the move can be taken again from where it lands. (oneOutcome_of_reading, erasesNothing_of_reading) a move
 that is a re-reading has one outcome, and erases nothing when the re-reading is one to one.
 (undone_of_reading) so on finitely many places such a move is undone from where it lands.
 (goesOn_of_lands_on_a_reading) the same first conclusion when each move lands on some re-reading of where
 it started under which admission is unchanged, the re-reading being allowed to differ from move to move.
reading: of the three conditions of pass 50, the first two follow from one sentence about readings, for a
 move that is itself a re-reading. The step from the sentence to "can be taken again" is two lines; the
 content is in the sentence.
not_claimed: that admission does not depend on the reading; that a physical move is a re-reading; that
 either follows from the declared inputs.
-/
import Definitions.Def_APFPaper5_K3_ReadingInvariance
import Theorems.Thm_APFPaper5_K3_undone_of_erases_nothing_and_goes_on
import Theorems.Thm_APFPaper5_K3_undone_of_each_kind
import Theorems.Thm_APFPaper5_K3_undoneWhereItLands_of_turnsLoseNothing
import Theorems.Thm_APFPaper5_K3_erasing_is_not_undone
import Theorems.Thm_APFPaper5_K3_one_way_is_not_undone
import Theorems.Thm_APFPaper5_K3_endless_is_not_undone

set_option autoImplicit false
namespace APFPaper5.K3

universe u

theorem goesOn_of_reading {N : Type u} (mv : N → N → Prop) (sigma : N → N)
    (hm : MoveIsReading mv sigma) (ha : AdmittedUnderReading mv sigma) : GoesOn mv := by
  intro a b hab
  have h := ha a b hab
  rw [← hm a b hab] at h
  exact ⟨sigma b, h⟩

theorem oneOutcome_of_reading {N : Type u} (mv : N → N → Prop) (sigma : N → N)
    (hm : MoveIsReading mv sigma) : OneOutcome mv :=
  fun a b b' h1 h2 => (hm a b h1).trans (hm a b' h2).symm

theorem erasesNothing_of_reading {N : Type u} (mv : N → N → Prop) (sigma : N → N)
    (hs : Function.Injective sigma) (hm : MoveIsReading mv sigma) : ErasesNothing mv :=
  fun a a' b h1 h2 => hs ((hm a b h1).symm.trans (hm a' b h2))

theorem undone_of_reading {N : Type u} [Finite N] (mv : N → N → Prop) (sigma : N → N)
    (hs : Function.Injective sigma) (hm : MoveIsReading mv sigma)
    (ha : AdmittedUnderReading mv sigma) : UndoneWhereItLands mv :=
  undone_of_erases_nothing_and_goes_on mv (oneOutcome_of_reading mv sigma hm)
    (erasesNothing_of_reading mv sigma hs hm) (goesOn_of_reading mv sigma hm ha)

theorem goesOn_of_lands_on_a_reading {N : Type u} (mv : N → N → Prop)
    (h : ∀ a b : N, mv a b →
      ∃ sigma : N → N, (∀ c d : N, mv c d → mv (sigma c) (sigma d)) ∧ sigma a = b) :
    GoesOn mv := by
  intro a b hab
  obtain ⟨sigma, hinv, hab'⟩ := h a b hab
  have h1 := hinv a b hab
  rw [hab'] at h1
  exact ⟨sigma b, h1⟩

end APFPaper5.K3


universe apfNative_u
theorem solution :
∀ {N : Type apfNative_u} (mv : N → N → Prop) (sigma : N → N)
  (hm : @APFPaper5.K3.MoveIsReading.{apfNative_u} N mv sigma), @APFPaper5.K3.OneOutcome.{apfNative_u} N mv := by
  exact @APFPaper5.K3.oneOutcome_of_reading
