-- Prove2me | solution 1 for APFPaper1.RecordBook.at_most_two_pairs_differ
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:53:33.005521+00:00
-- url     : https://prove2.me/submissions/16c3243b-57f0-44a0-8c45-772bdf5a7f23

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_triangle_obstruction
title: Three two-valued marks cannot be pairwise different
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:3666-3691 (Example early-micro-example, IJC panel).
consumes_inputs: none.
statement: (no_three_pairwise_different) no three Boolean values are pairwise different.
 (at_most_two_pairs_differ) among the pairs ab, bc, ca at most two differ. (no_atom_all_different) no atom
 of any record space gives three Boolean events pairwise different values. (no_perfect_triangle) three
 Boolean events cannot each pair disagree at every atom of a nonempty set of atoms.
not_claimed: the weighted form over state weights (the Supplement's bound of 2 on the sum of the three
 disagreement probabilities) is not stated here; it follows from at_most_two_pairs_differ by averaging.
-/
import Mathlib.Data.Set.Defs

set_option autoImplicit false
namespace APFPaper1.RecordBook

universe uA

theorem no_three_pairwise_different (a b c : Bool) : ¬ (a ≠ b ∧ b ≠ c ∧ c ≠ a) := by
  cases a <;> cases b <;> cases c <;> simp

theorem at_most_two_pairs_differ (a b c : Bool) :
    (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) + (if c ≠ a then 1 else 0) ≤ (2 : Nat) := by
  cases a <;> cases b <;> cases c <;> decide

theorem no_atom_all_different {Atom : Type uA} (A B C : Atom → Bool) :
    ¬ ∃ w : Atom, A w ≠ B w ∧ B w ≠ C w ∧ C w ≠ A w :=
  fun ⟨w, h⟩ => no_three_pairwise_different (A w) (B w) (C w) h

theorem no_perfect_triangle {Atom : Type uA} (A B C : Atom → Bool) (atoms : Set Atom)
    (hne : atoms.Nonempty)
    (hAB : ∀ w ∈ atoms, A w ≠ B w) (hBC : ∀ w ∈ atoms, B w ≠ C w)
    (hCA : ∀ w ∈ atoms, C w ≠ A w) : False := by
  obtain ⟨w, hw⟩ := hne
  exact no_three_pairwise_different (A w) (B w) (C w) ⟨hAB w hw, hBC w hw, hCA w hw⟩

end APFPaper1.RecordBook


theorem solution :
∀ (a b c : Bool),
  LE.le.{0}
    (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (ite.{1} (Ne.{1} a b) 1 0) (ite.{1} (Ne.{1} b c) 1 0))
      (ite.{1} (Ne.{1} c a) 1 0))
    2 := by
  exact @APFPaper1.RecordBook.at_most_two_pairs_differ
