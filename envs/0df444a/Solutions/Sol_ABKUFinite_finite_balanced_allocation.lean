-- Prove2me | solution 1 for ABKUFinite.finite_balanced_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T12:22:50.536277+00:00
-- url     : https://prove2.me/submissions/7296140a-d016-4ef6-b8e0-33a8ab0d0296

import Mathlib
import Definitions.Def_ABKUFinite_Model
import Theorems.Thm_ABKUFinite_theorem_3_2
import Theorems.Thm_ABKUFinite_theorem_3_3

set_option autoImplicit false

namespace ABKUReduction

open ABKUFinite

/-- Union bound for the uniform counting probability: `P(A ∧ B) ≥ P(A) + P(B) - 1`. -/
lemma prob_and (n d : ℕ) (A B : Trace n d → Prop) :
    probability n d A + probability n d B - 1 ≤ probability n d (fun w => A w ∧ B w) := by
  classical
  unfold probability
  simp only [Fintype.card_subtype]
  have hpos : (0 : ℝ) < Fintype.card (Trace n d) := by exact_mod_cast Fintype.card_pos
  have h := Finset.card_union_add_card_inter (Finset.univ.filter A) (Finset.univ.filter B)
  rw [← Finset.filter_or, ← Finset.filter_and] at h
  have hu := Finset.card_le_univ (Finset.univ.filter (fun w => A w ∨ B w))
  have key : ((Finset.univ.filter A).card : ℝ) + (Finset.univ.filter B).card
      ≤ (Finset.univ.filter (fun w => A w ∧ B w)).card + Fintype.card (Trace n d) := by
    exact_mod_cast (by omega)
  rw [← add_div, div_sub_one hpos.ne']
  gcongr
  linarith

/-- Monotonicity of the uniform counting probability. -/
lemma prob_mono (n d : ℕ) (A B : Trace n d → Prop) (h : ∀ w, A w → B w) :
    probability n d A ≤ probability n d B := by
  classical
  unfold probability
  simp only [Fintype.card_subtype]
  have hpos : (0 : ℝ) < Fintype.card (Trace n d) := by exact_mod_cast Fintype.card_pos
  gcongr
  exact h _

end ABKUReduction

open ABKUFinite in
theorem solution (d : ℕ) : TwoSided d := by
  obtain ⟨C1, hC1, h1⟩ := ABKUFinite.theorem_3_2 d
  obtain ⟨C2, hC2, h2⟩ := ABKUFinite.theorem_3_3 d
  refine ⟨max C1 C2, le_max_of_le_left hC1, fun ε hε => ?_⟩
  obtain ⟨N1, hN1⟩ := h1 (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := h2 (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have a := hN1 n (le_of_max_le_left hn)
  have b := hN2 n (le_of_max_le_right hn)
  have c := ABKUReduction.prob_and n d
    (fun w => (maxLoad n d w : ℝ) ≤ center n d + C1)
    (fun w => center n d - C2 ≤ (maxLoad n d w : ℝ))
  have m := ABKUReduction.prob_mono n d
    (fun w => (maxLoad n d w : ℝ) ≤ center n d + C1 ∧ center n d - C2 ≤ (maxLoad n d w : ℝ))
    (fun w => |(maxLoad n d w : ℝ) - center n d| ≤ max C1 C2)
    (fun w hw => abs_le.2 ⟨by linarith [hw.2, le_max_right C1 C2],
      by linarith [hw.1, le_max_left C1 C2]⟩)
  linarith
