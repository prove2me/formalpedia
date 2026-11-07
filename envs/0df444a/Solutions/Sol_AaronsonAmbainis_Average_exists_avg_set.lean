-- Prove2me | solution 1 for AaronsonAmbainis.Average.exists_avg_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:46:03.627893+00:00
-- url     : https://prove2.me/submissions/c0fa09ee-f2cd-4efb-847a-aa94f4c26d61

import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Theorems.Thm_AaronsonAmbainis_Average_inflR_avg_le
import Theorems.Thm_AaronsonAmbainis_Average_meanAbsIncr_avg_le
import Theorems.Thm_AaronsonAmbainis_Average_meanAbsIncr_avg_self
import Theorems.Thm_AaronsonAmbainis_Average_rows_avg
import Theorems.Thm_AaronsonAmbainis_Average_variance_avg
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K : ℝ} (ha : ∀ x i, 0 ≤ a x i)
    (hsum : ∀ x, ∑ i, a x i ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i)
    (R : Finset ι) :
    ∃ (g : Cube ι → ℝ) (b : Cube ι → ι → ℝ),
      (∀ x i, 0 ≤ b x i) ∧ (∀ x, ∑ i, b x i ≤ K) ∧
      (∀ x y, |g x - g y| ≤ ∑ i ∈ diffSet x y, b x i) ∧
      variance f ≤ variance g + ∑ j ∈ R, inflR f j ∧
      (∀ k, inflR g k ≤ inflR f k) ∧ (∀ k, meanAbsIncr g k ≤ meanAbsIncr f k) ∧
      (∀ j ∈ R, meanAbsIncr g j = 0) := by
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨f, a, ha, hsum, hrow, ?_, fun k => le_refl _, fun k => le_refl _,
      fun j hj => absurd hj (Finset.notMem_empty j)⟩
    rw [Finset.sum_empty, add_zero]
  | insert j R hjR ih =>
    obtain ⟨g, b, hb0, hbK, hbrow, hvar, hR2, hL1, hzero⟩ := ih
    obtain ⟨hb0', hbK', hbrow'⟩ := rows_avg j hb0 hbK hbrow
    refine ⟨avg j g, fun x i => (b x i + b (flipSet x {j}) i) / 2, hb0', hbK', hbrow',
      ?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_insert hjR]
      have h1 := variance_avg j g
      have h2 := hR2 j
      linarith
    · intro k
      exact le_trans (inflR_avg_le j k g) (hR2 k)
    · intro k
      exact le_trans (meanAbsIncr_avg_le j k g) (hL1 k)
    · intro i hi
      rcases Finset.mem_insert.mp hi with h | hiR
      · rw [h]
        exact meanAbsIncr_avg_self j g
      · exact le_antisymm (le_trans (meanAbsIncr_avg_le j i g) (le_of_eq (hzero i hiR)))
          (Level.meanAbsIncr_nonneg _ _)
end AaronsonAmbainis.Average
