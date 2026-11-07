-- Prove2me | solution 1 for AaronsonAmbainis.overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:36:09.686732+00:00
-- url     : https://prove2.me/submissions/1f3cb823-70df-4991-944b-22d8a5af036b

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Theorems.Thm_AaronsonAmbainis_mem_diffSet


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution {g : Cube ι → Bool} {p q : Cube ι} (hpq : g p ≠ g q) {x y : ι → ℝ}
    (hx : IsRow g p x) (hy : IsRow g q y) :
    1 ≤ ∑ j ∈ diffSet p q, min (x j) (y j) := by
  -- `T` is the set `S` of the proof in the paper: `{j ∈ Δ : x_j ≤ y_j}`
  obtain ⟨T, hT⟩ : ∃ T : Finset ι, T = (diffSet p q).filter (fun j => x j ≤ y j) := ⟨_, rfl⟩
  have hTsub : T ⊆ diffSet p q := by
    rw [hT]
    exact Finset.filter_subset _ _
  -- `p^T = q^(Δ \ T)`
  have hr : flipSet p T = flipSet q (diffSet p q \ T) := by
    funext i
    simp only [flipSet]
    by_cases hi : i ∈ diffSet p q
    · have hpi : p i ≠ q i := mem_diffSet.mp hi
      by_cases hiT : i ∈ T
      · have hiT' : i ∉ diffSet p q \ T := fun h => (Finset.mem_sdiff.mp h).2 hiT
        rw [if_pos hiT, if_neg hiT']
        cases hp : p i <;> cases hq : q i <;> simp_all
      · have hiT' : i ∈ diffSet p q \ T := Finset.mem_sdiff.mpr ⟨hi, hiT⟩
        rw [if_neg hiT, if_pos hiT']
        cases hp : p i <;> cases hq : q i <;> simp_all
    · have hpi : p i = q i := by
        by_contra h
        exact hi (mem_diffSet.mpr h)
      have h1 : i ∉ T := fun h => hi (hTsub h)
      have h2 : i ∉ diffSet p q \ T := fun h => hi (Finset.mem_sdiff.mp h).1
      rw [if_neg h1, if_neg h2, hpi]
  -- the sum of minima is `y(Δ \ T) + x(T)`
  have hsplit : ∑ j ∈ diffSet p q \ T, y j + ∑ j ∈ T, x j
      = ∑ j ∈ diffSet p q, min (x j) (y j) := by
    rw [← Finset.sum_sdiff hTsub]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hjΔ, hjT⟩ := Finset.mem_sdiff.mp hj
      have hnot : ¬ x j ≤ y j := fun h => hjT (by rw [hT]; exact Finset.mem_filter.mpr ⟨hjΔ, h⟩)
      exact (min_eq_right (le_of_not_ge hnot)).symm
    · apply Finset.sum_congr rfl
      intro j hj
      rw [hT] at hj
      exact (min_eq_left (Finset.mem_filter.mp hj).2).symm
  rw [← hsplit]
  have hxT : 0 ≤ ∑ j ∈ T, x j := Finset.sum_nonneg fun j _ => hx.1 j
  have hyT : 0 ≤ ∑ j ∈ diffSet p q \ T, y j := Finset.sum_nonneg fun j _ => hy.1 j
  by_cases hg : g (flipSet p T) = g p
  · have hne : g (flipSet q (diffSet p q \ T)) ≠ g q := by
      rw [← hr, hg]
      exact hpq
    have h1 := hy.2 _ hne
    linarith
  · have h1 := hx.2 T hg
    linarith
end AaronsonAmbainis
