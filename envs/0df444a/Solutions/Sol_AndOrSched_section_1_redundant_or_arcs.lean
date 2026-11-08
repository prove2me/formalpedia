-- Prove2me | solution 1 for AndOrSched.section_1_redundant_or_arcs
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:21:40.731111+00:00
-- url     : https://prove2.me/submissions/8c4e44ff-1f72-4ba1-8c65-1d9f93060997

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_nonRedPred
import Definitions.Def_AndOrSched_reduceOr
open scoped Classical NNReal

namespace Aux_AndOr_red
open AndOrSched

theorem hmono (I : Instance) (C : I.N → ℝ) (hC : IsFeasible I C) :
    ∀ x y, Relation.TransGen I.andA x y → C (Sum.inl x) ≤ C (Sum.inl y) := by
  intro x y h
  induction h with
  | @single b hxy =>
    have := hC.2.2.1 (Sum.inl x) (Sum.inl b) hxy
    have hp : (0 : ℝ) ≤ ((I.p (Sum.inl b) : ℚ≥0) : ℝ) := by positivity
    linarith
  | @tail b c _ hbc ih =>
    have := hC.2.2.1 (Sum.inl b) (Sum.inl c) hbc
    have hp : (0 : ℝ) ≤ ((I.p (Sum.inl c) : ℚ≥0) : ℝ) := by positivity
    linarith

theorem hmin (I : Instance) (hI : Acyclic I) (b : I.B) (a : I.A) (ha : a ∈ orPred I b) :
    ∃ a' ∈ nonRedPred I b, a' = a ∨ Relation.TransGen I.andA a' a := by
  haveI : IsTrans I.A (Relation.TransGen I.andA) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  haveI : Std.Irrefl (Relation.TransGen I.andA) := ⟨hI.1⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen I.andA)
  obtain ⟨a', ⟨ha'1, ha'2⟩, hm⟩ := wf.has_min
    {x | x ∈ orPred I b ∧ (x = a ∨ Relation.TransGen I.andA x a)} ⟨a, ha, Or.inl rfl⟩
  refine ⟨a', ?_, ha'2⟩
  simp only [nonRedPred, Finset.mem_filter]
  refine ⟨ha'1, ?_⟩
  rintro ⟨a'', ha''1, _, hrel⟩
  apply hm a'' ⟨ha''1, Or.inr ?_⟩ hrel
  rcases ha'2 with rfl | h
  · exact hrel
  · exact hrel.trans h

end Aux_AndOr_red

open AndOrSched Aux_AndOr_red in
theorem solution (I : Instance) (hI : Acyclic I) :
    (∀ C : I.N → ℝ, IsFeasible I C ↔ IsFeasible (reduceOr I) C) ∧
    ∀ b, nonRedPred (reduceOr I) b = orPred (reduceOr I) b := by
  have hand : andRel (reduceOr I) = andRel I := by
    funext i j; cases i <;> cases j <;> rfl
  have hor : ∀ b, orPred (reduceOr I) b = nonRedPred I b := by
    intro b; ext a; unfold orPred; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]; rfl
  have hsub : ∀ b, nonRedPred I b ⊆ orPred I b := fun b => Finset.filter_subset _ _
  constructor
  · intro C
    constructor
    · intro hC
      obtain ⟨h1, h2, h3, h4⟩ := hC
      refine ⟨h1, h2, by rw [hand]; exact h3, fun b hb => ?_⟩
      rw [hor b] at hb ⊢
      obtain ⟨a, ha, hCa⟩ := h4 b (hb.mono (hsub b))
      obtain ⟨a', ha', hrel⟩ := hmin I hI b a ha
      refine ⟨a', ha', ?_⟩
      change C (Sum.inl a') + ((I.p (Sum.inr b) : ℚ≥0) : ℝ) ≤ C (Sum.inr b)
      rcases hrel with rfl | hrel
      · exact hCa
      · have := hmono I C ⟨h1, h2, h3, h4⟩ a' a hrel
        linarith
    · intro hC
      obtain ⟨h1, h2, h3, h4⟩ := hC
      rw [hand] at h3
      refine ⟨h1, h2, h3, fun b hb => ?_⟩
      obtain ⟨a, ha⟩ := hb
      obtain ⟨a', ha', _⟩ := hmin I hI b a ha
      obtain ⟨a'', ha'', hC⟩ := h4 b (by rw [hor b]; exact ⟨a', ha'⟩)
      rw [hor b] at ha''
      exact ⟨a'', hsub b ha'', hC⟩
  · intro b
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro a ha
    simp only [nonRedPred, Finset.mem_filter]
    refine ⟨ha, ?_⟩
    rintro ⟨a', ha', hne, hrel⟩
    rw [hor b] at ha ha'
    unfold nonRedPred at ha
    have ha2 := (Finset.mem_filter.mp ha).2
    exact ha2 ⟨a', hsub b ha', hne, hrel⟩
