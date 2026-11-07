-- Prove2me | solution 1 for AaronsonAmbainis.Row.not_blockInequality_without_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:34:56.351516+00:00
-- url     : https://prove2.me/submissions/c12831c2-21cf-439f-b8c1-34d2c7868c5e

import Definitions.Def_AaronsonAmbainis_Row_Main
import Definitions.Def_AaronsonAmbainis_Row_HypothesisCheck
import Theorems.Thm_AaronsonAmbainis_Row_abs_sgn
import Theorems.Thm_AaronsonAmbainis_Row_chi_eq_prod_sgn
import Theorems.Thm_AaronsonAmbainis_Row_chi_flipSet
import Theorems.Thm_AaronsonAmbainis_Row_chi_zero
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_chi
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
namespace AaronsonAmbainis.Row
theorem _root_.solution :
    ¬ (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
        HasDegreeLE f d →
      ∀ (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι) (N m : ℕ),
        (∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) →
        (N : ℝ) * (1 - Real.cos (Real.pi / (m : ℝ))) ≤ 2 →
        ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 * (m : ℝ) ^ 2) := by
  intro h
  have hf : ∀ x : Cube Unit, |chi ({()} : Finset Unit) x| ≤ 1 := by
    intro x
    rw [chi_eq_prod_sgn, Finset.prod_singleton]
    exact (abs_sgn _).le
  have hdeg : HasDegreeLE (chi ({()} : Finset Unit)) 1 :=
    hasDegreeLE_chi ({()} : Finset Unit) (by simp)
  have hc : ((1 : ℕ) : ℝ) * (1 - Real.cos (Real.pi / ((0 : ℕ) : ℝ))) ≤ 2 := by
    rw [Nat.cast_zero, div_zero, Real.cos_zero, sub_self, mul_zero]
    norm_num
  have h1 := h Unit 1 (chi {()}) hf hdeg (zero Unit) Unit (fun _ => {()}) 1 0
    (fun i => Finset.card_le_one_of_subsingleton _) hc
  have e2 : chi ({()} : Finset Unit) (flipSet (zero Unit) {()}) = -1 := by
    rw [chi_flipSet, Finset.prod_singleton]
    simp [zero]
  simp only [Fintype.sum_unique, chi_zero, e2] at h1
  have h2 : (1 : ℝ) - -1 ≤ 4 * ((1 : ℕ) : ℝ) ^ 2 * ((0 : ℕ) : ℝ) ^ 2 := (le_abs_self _).trans h1
  norm_num at h2
end AaronsonAmbainis.Row
