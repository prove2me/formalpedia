-- Prove2me | solution 1 for AssortOpt.HMF.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:14:10.440371+00:00
-- url     : https://prove2.me/submissions/398ff0d1-f65f-4fbb-bcbb-1c86b8b1de39

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

open AssortOpt.HMF

theorem solution {n : ℕ} (D : ListDist n) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (x : List (Fin n) → Fin n → ℝ) (hx : IsIC D x) (f : Finset (Fin n) → ℝ)
    (hf : ∀ S : Finset (Fin n),
      IsGreatest ((fun ℓ => ∑ j ∈ S ∩ ℓ.toFinset, x ℓ j) '' (D.supp : Set (List (Fin n)))) (f S)) :
    IsIncreasingSetFn f ∧
    (∀ ℓ ∈ D.supp, ∀ k : Fin ℓ.length,
      x ℓ (ℓ.get k) = f (ℓ.take (k + 1)).toFinset - f (ℓ.take k).toFinset) ∧
    revSetFn D r f = revMech D r x ∧
    (∃ g : Finset (Fin n) → ℝ, IsIncreasingSetFn g ∧ revMech D r x ≤ revSetFn D r g) := by
  classical
  obtain ⟨h3, h4, h5⟩ := hx
  -- f S is attained at some list of the support
  have hatt : ∀ S, ∃ ℓ0 ∈ D.supp, f S = ∑ j ∈ S ∩ ℓ0.toFinset, x ℓ0 j := by
    intro S
    obtain ⟨⟨ℓ0, hℓ0, he⟩, -⟩ := hf S
    exact ⟨ℓ0, hℓ0, he.symm⟩
  have hub : ∀ S, ∀ ℓ ∈ D.supp, ∑ j ∈ S ∩ ℓ.toFinset, x ℓ j ≤ f S := by
    intro S ℓ hℓ
    exact (hf S).2 ⟨ℓ, hℓ, rfl⟩
  have hnn : ∀ ℓ ∈ D.supp, ∀ A : Finset (Fin n), ∀ j ∈ A ∩ ℓ.toFinset, 0 ≤ x ℓ j := by
    intro ℓ hℓ A j hj
    exact h5 ℓ hℓ j (List.mem_toFinset.mp (Finset.mem_inter.mp hj).2)
  have hinc : IsIncreasingSetFn f := by
    refine ⟨fun S S' hSS' => ?_, fun S => ?_⟩
    · obtain ⟨ℓ0, hℓ0, he⟩ := hatt S
      rw [he]
      refine le_trans ?_ (hub S' ℓ0 hℓ0)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_inter_right hSS')
      intro j hj _
      exact hnn ℓ0 hℓ0 S' j hj
    · obtain ⟨ℓ0, hℓ0, he⟩ := hatt S
      rw [he]
      constructor
      · exact Finset.sum_nonneg (hnn ℓ0 hℓ0 S)
      · refine le_trans ?_ (h4 ℓ0 hℓ0)
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro j hj _
        exact h5 ℓ0 hℓ0 j (List.mem_toFinset.mp hj)
  -- (33): f on a prefix equals the allocated probability on it
  have h33 : ∀ ℓ ∈ D.supp, ∀ k ≤ ℓ.length,
      f (ℓ.take k).toFinset = ∑ j ∈ (ℓ.take k).toFinset, x ℓ j := by
    intro ℓ hℓ k hk
    apply le_antisymm
    · obtain ⟨ℓ0, hℓ0, he⟩ := hatt (ℓ.take k).toFinset
      rw [he]
      exact h3 ℓ hℓ k hk ℓ0 hℓ0
    · have := hub (ℓ.take k).toFinset ℓ hℓ
      have hint : (ℓ.take k).toFinset ∩ ℓ.toFinset = (ℓ.take k).toFinset := by
        apply Finset.inter_eq_left.mpr
        intro a ha
        rw [List.mem_toFinset] at ha ⊢
        exact List.mem_of_mem_take ha
      rwa [hint] at this
  have h8 : ∀ ℓ ∈ D.supp, ∀ k : Fin ℓ.length,
      x ℓ (ℓ.get k) = f (ℓ.take (k + 1)).toFinset - f (ℓ.take k).toFinset := by
    intro ℓ hℓ k
    have hnd := D.nodup ℓ hℓ
    rw [h33 ℓ hℓ (k + 1) k.2, h33 ℓ hℓ k (le_of_lt k.2)]
    rw [List.sum_toFinset _ (hnd.sublist (List.take_sublist _ _)),
      List.sum_toFinset _ (hnd.sublist (List.take_sublist _ _))]
    rw [List.take_add_one, List.getElem?_eq_getElem k.2]
    simp
  have hrev : revSetFn D r f = revMech D r x := by
    unfold revSetFn revMech
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    congr 1
    have hnd := D.nodup ℓ hℓ
    have e1 : ∀ k : Fin ℓ.length, r (ℓ.get k) * (f (ℓ.take (k + 1)).toFinset -
        f (ℓ.take k).toFinset) = (fun j => r j * x ℓ j) ℓ[k.1] := by
      intro k
      rw [← h8 ℓ hℓ k]
      rfl
    rw [Finset.sum_congr rfl (fun k _ => e1 k), List.sum_toFinset _ hnd]
    exact Fin.sum_univ_fun_getElem ℓ (fun j => r j * x ℓ j)
  exact ⟨hinc, h8, hrev, f, hinc, hrev.ge⟩
