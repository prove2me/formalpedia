-- Prove2me | solution 1 for ApproxCliqueWidth.Certificate.fmin_isInterpolation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:50:37.567402+00:00
-- url     : https://prove2.me/submissions/fba1df7c-a34f-4bee-a5d9-b2153be0018d

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation

namespace ApproxCliqueWidth.Certificate

theorem aux_fmi_le {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (X Y Z : Finset V) (hXZ : X ⊆ Z) (hZY : Disjoint Z Y) :
    fmin f X Y ≤ f Z := by
  unfold fmin
  have hmem : Z ∈ Finset.univ.filter (fun Z : Finset V => X ⊆ Z ∧ Disjoint Z Y) := by
    simp [hXZ, hZY]
  rw [dif_pos ⟨Z, hmem⟩]
  exact Finset.inf'_le f hmem

theorem aux_fmi_eq {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (X Y : Finset V) (hXY : Disjoint X Y) :
    ∃ Z, X ⊆ Z ∧ Disjoint Z Y ∧ fmin f X Y = f Z := by
  unfold fmin
  have hmem : X ∈ Finset.univ.filter (fun Z : Finset V => X ⊆ Z ∧ Disjoint Z Y) := by
    simp [hXY]
  rw [dif_pos ⟨X, hmem⟩]
  obtain ⟨Z, hZ, hZeq⟩ := Finset.exists_mem_eq_inf' ⟨X, hmem⟩ f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hZ
  exact ⟨Z, hZ.1, hZ.2, hZeq⟩

theorem aux_fmi_main {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (hsub : IsSubmodular f) (hmin : ∀ X : Finset V, f ∅ ≤ f X) :
    IsInterpolation f (fmin f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X
    obtain ⟨Z, hXZ, hZY, heq⟩ := aux_fmi_eq f X Xᶜ disjoint_compl_right
    have : Z = X := by
      apply le_antisymm _ hXZ
      intro v hv
      by_contra hvX
      exact Finset.disjoint_left.mp hZY hv (Finset.mem_compl.mpr hvX)
    rw [heq, this]
  · intro A B C D hCD hAC hBD
    obtain ⟨Z, hCZ, hZD, heq⟩ := aux_fmi_eq f C D hCD
    rw [heq]
    exact aux_fmi_le f A B Z (hAC.trans hCZ) (Finset.disjoint_of_subset_right hBD hZD)
  · intro A B C D hAB hCD
    obtain ⟨Z1, hAZ1, hZ1B, heq1⟩ := aux_fmi_eq f A B hAB
    obtain ⟨Z2, hCZ2, hZ2D, heq2⟩ := aux_fmi_eq f C D hCD
    rw [heq1, heq2]
    have h1 : fmin f (A ∩ C) (B ∪ D) ≤ f (Z1 ∩ Z2) := by
      apply aux_fmi_le
      · exact Finset.inter_subset_inter hAZ1 hCZ2
      · rw [Finset.disjoint_union_right]
        exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_left hZ1B,
          Finset.disjoint_of_subset_left Finset.inter_subset_right hZ2D⟩
    have h2 : fmin f (A ∪ C) (B ∩ D) ≤ f (Z1 ∪ Z2) := by
      apply aux_fmi_le
      · exact Finset.union_subset_union hAZ1 hCZ2
      · rw [Finset.disjoint_union_left]
        exact ⟨Finset.disjoint_of_subset_right Finset.inter_subset_left hZ1B,
          Finset.disjoint_of_subset_right Finset.inter_subset_right hZ2D⟩
    have h3 := hsub Z1 Z2
    omega
  · apply le_antisymm
    · exact aux_fmi_le f ∅ ∅ ∅ (le_refl _) (Finset.disjoint_empty_left _)
    · obtain ⟨Z, _, _, heq⟩ := aux_fmi_eq f ∅ ∅ (Finset.disjoint_empty_left _)
      rw [heq]
      exact hmin Z

end ApproxCliqueWidth.Certificate

open ApproxCliqueWidth.Certificate

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (hsub : IsSubmodular f) (hmin : ∀ X : Finset V, f ∅ ≤ f X) :
    IsInterpolation f (fmin f) :=
  aux_fmi_main f hsub hmin
