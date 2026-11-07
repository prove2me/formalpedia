-- Prove2me | solution 1 for AaronsonAmbainis.twoSided_of_allPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:46:04.082328+00:00
-- url     : https://prove2.me/submissions/266b9b6c-41a4-4c65-818c-3bb01395d616

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_TwoSided_RemoveWeights
import Theorems.Thm_AaronsonAmbainis_final_arith
import Theorems.Thm_AaronsonAmbainis_abstract_cs
import Theorems.Thm_AaronsonAmbainis_overlap_pos
import Theorems.Thm_AaronsonAmbainis_two_mul_bdry


set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution : AllPairsInequality → TwoSidedInequality := by
  intro hAllPairs ι _ _ g lam hlam τ hτ hinfl
  have h2n : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hC : 0 ≤ (2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4 :=
    div_nonneg (mul_nonneg (mul_nonneg h2n.le h2n.le) hτ) (by norm_num)
  -- every boundary is at most `2 ^ n * τ / 2`
  have hb : ∀ j, (bdry g j : ℝ) ≤ 2 ^ Fintype.card ι * τ / 2 := by
    intro j
    have h1 := two_mul_bdry g j
    have h2 := mul_le_mul_of_nonneg_left (hinfl j) h2n.le
    linarith
  -- the all-pairs inequality with the influence bound
  have hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
        ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹
        ≤ (2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4 * ∑ j, (w j)⁻¹ := by
    intro w hw
    have h1 := hAllPairs ι g w hw lam hlam
    have h3 : ∑ j, (bdry g j : ℝ) / w j ≤ 2 ^ Fintype.card ι * τ / 2 * ∑ j, (w j)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hb j) (inv_pos.mpr (hw j)).le
    have h4 : (2 : ℝ) ^ Fintype.card ι * ∑ j, (bdry g j : ℝ) / w j
        ≤ 2 ^ Fintype.card ι * (2 ^ Fintype.card ι * τ / 2 * ∑ j, (w j)⁻¹) :=
      mul_le_mul_of_nonneg_left h3 h2n.le
    have h5 : (2 : ℝ) ^ Fintype.card ι * (2 ^ Fintype.card ι * τ / 2 * ∑ j, (w j)⁻¹)
        = 2 * ((2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4 * ∑ j, (w j)⁻¹) := by
      ring
    linarith
  -- positivity of the denominators: the overlap lemma
  have hpos : ∀ x ∈ univ.filter (fun x : Cube ι => g x = true),
      ∀ y ∈ univ.filter (fun y : Cube ι => g y = false),
      ∀ w : ι → ℝ, (∀ j, 0 < w j) → 0 < ∑ j ∈ diffSet x y, w j * lam x j * lam y j := by
    intro x hx y hy w hw
    have hgx : g x = true := (Finset.mem_filter.mp hx).2
    have hgy : g y = false := (Finset.mem_filter.mp hy).2
    have hne : g x ≠ g y := by
      intro h
      rw [hgx, hgy] at h
      exact Bool.noConfusion h
    exact overlap_pos hne (hlam x) (hlam y) hw
  have key := abstract_cs (univ.filter fun x : Cube ι => g x = true)
    (univ.filter fun y : Cube ι => g y = false) lam lam
    (fun x j => (hlam x).1 j) (fun y j => (hlam y).1 j) diffSet
    ((2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4) hC hpos hpairs
  exact final_arith h2n key
end AaronsonAmbainis
