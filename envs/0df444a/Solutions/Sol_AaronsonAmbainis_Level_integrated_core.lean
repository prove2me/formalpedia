-- Prove2me | solution 1 for AaronsonAmbainis.Level.integrated_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:12.763445+00:00
-- url     : https://prove2.me/submissions/30336dc2-98bc-436b-a2ac-5e7e27c2f0da

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_Level_Integrated
import Theorems.Thm_AaronsonAmbainis_Level_bdry_lev
import Theorems.Thm_AaronsonAmbainis_Level_level_allPairs
import Theorems.Thm_AaronsonAmbainis_Level_level_integration


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    2 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j := by
  have key := level_integration (univ : Finset (Cube ι × Cube ι)) (univ : Finset (ι × Cube ι))
    (fun z => 2 * (∑ j ∈ diffSet z.1 z.2, w j * a z.1 j * a z.2 j)⁻¹)
    (fun z => f z.1) (fun z => f z.2)
    (fun k => 2 ^ Fintype.card ι / w k.1) (fun k => f (flipSet k.2 {k.1})) (fun k => f k.2) ?_
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at key
    calc 2 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
        = ∑ x, ∑ y, 2 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
            * (max (f x - f y) 0 ^ 3 / 6) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
      _ ≤ ∑ j, ∑ x, 2 ^ Fintype.card ι / w j * max (f x - f (flipSet x {j})) 0 := key
      _ = 2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_div, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
  · intro t
    have h := level_allPairs hAllPairs f a ha hrow w hw t
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc ∑ x, ∑ y, 2 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
            * (max (f x - t) 0 * max (t - f y) 0)
        = 2 * ∑ x, ∑ y, max (f x - t) 0 * max (t - f y) 0
            * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
      _ ≤ 2 ^ Fintype.card ι * ∑ j, (bdry (lev f t) j : ℝ) / w j := h
      _ = ∑ j, ∑ x, 2 ^ Fintype.card ι / w j
            * (if f (flipSet x {j}) ≤ t ∧ t < f x then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [bdry_lev, Finset.sum_div, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
end AaronsonAmbainis.Level
