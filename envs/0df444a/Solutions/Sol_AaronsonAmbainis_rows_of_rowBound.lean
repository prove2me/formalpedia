-- Prove2me | solution 1 for AaronsonAmbainis.rows_of_rowBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:05:37.317799+00:00
-- url     : https://prove2.me/submissions/f8ceec05-1ff0-4812-a2f3-91968a11ed3f

import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Theorems.Thm_AaronsonAmbainis_Level_abs_incr_le_of_rows
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_add
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const_mul


set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution (hRB : RowBound) {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d) :
    ∃ a : Cube ι → ι → ℝ, (∀ x i, 0 ≤ a x i) ∧
      (∀ x, ∑ i, a x i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 / 2) ∧
      ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i := by
  -- `(1 + f)/2` has degree at most `d` and takes values in `[0,1]`
  have hdeg' : HasDegreeLE (fun x => 1 / 2 + 1 / 2 * f x) d :=
    Row.hasDegreeLE_add (Row.hasDegreeLE_const (1 / 2) d)
      (Row.hasDegreeLE_const_mul (1 / 2) hdeg)
  have hr : ∀ x, 0 ≤ 1 / 2 + 1 / 2 * f x ∧ 1 / 2 + 1 / 2 * f x ≤ 1 := by
    intro x
    have h1 := abs_le.mp (hf x)
    constructor <;> linarith [h1.1, h1.2]
  obtain ⟨c, hc1, hc2⟩ := hRB ι d (fun x => 1 / 2 + 1 / 2 * f x) hr hdeg'
  -- the weights are nonnegative: take `y = x^i`
  have hnn : ∀ x i, 0 ≤ c x i := fun x i =>
    le_trans (abs_nonneg _) (Level.abs_incr_le_of_rows hc1 x i)
  refine ⟨fun x i => 2 * c x i, fun x i => mul_nonneg (by norm_num) (hnn x i),
    fun x => ?_, fun x y => ?_⟩
  · have h2 := hc2 x
    rw [← Finset.mul_sum]
    linarith
  · have h1 : |(1 / 2 + 1 / 2 * f x) - (1 / 2 + 1 / 2 * f y)| ≤ ∑ i ∈ diffSet x y, c x i :=
      hc1 x y
    have e : (1 / 2 + 1 / 2 * f x) - (1 / 2 + 1 / 2 * f y) = (f x - f y) / 2 := by ring
    rw [e, abs_div, abs_two] at h1
    rw [← Finset.mul_sum]
    linarith
end AaronsonAmbainis
