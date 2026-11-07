-- Prove2me | solution 1 for AaronsonAmbainis.Level.exists_rows_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:43.239783+00:00
-- url     : https://prove2.me/submissions/5c21b8af-a162-407f-a78a-d42010c3bab9

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_mem_diffSet


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (f : Cube ι → ℝ) :
    ∃ (K : ℝ) (a : Cube ι → ι → ℝ), (∀ x j, 0 ≤ a x j) ∧ (∀ x, ∑ j, a x j ≤ K) ∧
      ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j := by
  have hnn : ∀ x : Cube ι, 0 ≤ ∑ z, |f x - f z| := fun x =>
    Finset.sum_nonneg (fun z _ => abs_nonneg _)
  refine ⟨∑ x : Cube ι, ∑ _j : ι, ∑ z, |f x - f z|, fun x _ => ∑ z, |f x - f z|,
    fun x _ => hnn x, fun x => ?_, fun x y => ?_⟩
  · exact Finset.single_le_sum (f := fun x : Cube ι => ∑ _j : ι, ∑ z, |f x - f z|)
      (fun x _ => Finset.sum_nonneg (fun _ _ => hnn x)) (Finset.mem_univ x)
  · by_cases hxy : x = y
    · rw [hxy, sub_self, abs_zero]
      exact Finset.sum_nonneg (fun _ _ => hnn y)
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra hcon
        exact hxy (funext (fun i => by_contra (fun h => hcon ⟨i, h⟩)))
      have hmem : i ∈ diffSet x y := mem_diffSet.mpr hi
      calc |f x - f y| ≤ ∑ z, |f x - f z| :=
            Finset.single_le_sum (f := fun z => |f x - f z|) (fun z _ => abs_nonneg _)
              (Finset.mem_univ y)
        _ ≤ ∑ _j ∈ diffSet x y, ∑ z, |f x - f z| :=
            Finset.single_le_sum (f := fun _ : ι => ∑ z, |f x - f z|) (fun _ _ => hnn x) hmem
end AaronsonAmbainis.Level
