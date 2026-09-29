-- Prove2me | solution 1 for ApproxCliqueWidth.Certificate.interpolation_properties
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:20:02.841829+00:00
-- url     : https://prove2.me/submissions/5e2298a3-6db2-48f7-abd4-1fb7aad39d93

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation

namespace ApproxCliqueWidth.Certificate

theorem aux_acwip_empty {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (fstar : Finset V → Finset V → ℤ) (hint : IsInterpolation f fstar)
    (Y : Finset V) : fstar ∅ Y = f ∅ := by
  obtain ⟨h1, h2, _, h4⟩ := hint
  apply le_antisymm
  · have := h2 ∅ Y ∅ (∅ : Finset V)ᶜ disjoint_compl_right (subset_refl _) (Finset.subset_univ _ |>.trans (by simp))
    rw [h1] at this
    exact this
  · rw [← h4]
    exact h2 ∅ ∅ ∅ Y (Finset.disjoint_empty_left _) (subset_refl _) (Finset.empty_subset _)

theorem aux_acwip_card {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (fstar : Finset V → Finset V → ℤ) (hint : IsInterpolation f fstar)
    (hunit : ∀ v : V, f {v} - f ∅ ≤ 1) (B : Finset V) :
    ∀ X : Finset V, X ⊆ Bᶜ → fstar X B - f ∅ ≤ (X.card : ℤ) := by
  intro X
  induction X using Finset.induction_on with
  | empty =>
    intro _
    rw [aux_acwip_empty f fstar hint B]
    simp
  | @insert v X' hv ih =>
    intro hX
    have hX' : X' ⊆ Bᶜ := (Finset.subset_insert v X').trans hX
    have hvB : v ∈ Bᶜ := hX (Finset.mem_insert_self v X')
    have ih' := ih hX'
    obtain ⟨h1, h2, h3, _⟩ := hint
    have hdv : Disjoint ({v} : Finset V) B := by
      rw [← Finset.subset_compl_iff_disjoint_right]
      simpa using hvB
    have hdX' : Disjoint X' B := Finset.subset_compl_iff_disjoint_right.mp hX'
    have hs := h3 {v} B X' B hdv hdX'
    have hinter : ({v} : Finset V) ∩ X' = ∅ := by
      rw [Finset.singleton_inter_of_notMem hv]
    have hunion : ({v} : Finset V) ∪ X' = insert v X' := by
      rw [Finset.insert_eq]
    rw [hinter, hunion, Finset.union_self, Finset.inter_self,
      aux_acwip_empty f fstar ⟨h1, h2, h3, ‹_›⟩ B] at hs
    have hvle : fstar {v} B ≤ f {v} := by
      have := h2 {v} B {v} ({v} : Finset V)ᶜ disjoint_compl_right (subset_refl _)
        (Finset.subset_compl_iff_disjoint_right.mpr hdv.symm)
      rw [h1] at this
      exact this
    have hu := hunit v
    rw [Finset.card_insert_of_notMem hv]
    push_cast
    linarith

end ApproxCliqueWidth.Certificate

open ApproxCliqueWidth.Certificate

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (hsub : IsSubmodular f) (hmin : ∀ X : Finset V, f ∅ ≤ f X)
    (fstar : Finset V → Finset V → ℤ) (hint : IsInterpolation f fstar) :
    (∀ X Y : Finset V, Disjoint X Y →
        ∀ Z : Finset V, X ⊆ Z → Disjoint Z Y → fstar X Y ≤ f Z) ∧
    (∀ Y : Finset V, fstar ∅ Y = f ∅) ∧
    ((∀ v : V, f {v} - f ∅ ≤ 1) →
        ∀ B : Finset V, IsMatroidRankOn Bᶜ (fun X => fstar X B - f ∅)) := by
  refine ⟨?_, aux_acwip_empty f fstar hint, ?_⟩
  · intro X Y _ Z hXZ hZY
    obtain ⟨h1, h2, _, _⟩ := hint
    have := h2 X Y Z Zᶜ disjoint_compl_right hXZ
      (Finset.subset_compl_iff_disjoint_right.mpr hZY.symm)
    rw [h1] at this
    exact this
  · intro hunit B
    refine ⟨?_, ?_, ?_⟩
    · intro X hX
      refine ⟨?_, aux_acwip_card f fstar hint hunit B X hX⟩
      have hd : Disjoint X B := Finset.subset_compl_iff_disjoint_right.mp hX
      have := hint.2.1 ∅ B X B hd (Finset.empty_subset _) (subset_refl _)
      rw [aux_acwip_empty f fstar hint B] at this
      simp only
      linarith
    · intro X Y hXY hY
      have hd : Disjoint Y B := Finset.subset_compl_iff_disjoint_right.mp hY
      have := hint.2.1 X B Y B hd hXY (subset_refl _)
      simp only
      linarith
    · intro X Y hX hY
      have hdX : Disjoint X B := Finset.subset_compl_iff_disjoint_right.mp hX
      have hdY : Disjoint Y B := Finset.subset_compl_iff_disjoint_right.mp hY
      have := hint.2.2.1 X B Y B hdX hdY
      rw [Finset.union_self, Finset.inter_self] at this
      simp only
      linarith
