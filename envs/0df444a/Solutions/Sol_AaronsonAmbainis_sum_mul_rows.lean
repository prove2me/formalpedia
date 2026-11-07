-- Prove2me | solution 1 for AaronsonAmbainis.sum_mul_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:18:42.884365+00:00
-- url     : https://prove2.me/submissions/7e9a7b3c-f48c-429e-afd0-32321fd77d87

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (w : ι → ℝ) (u : α → ℝ) (v : β → ℝ) (f : α → ι → ℝ) (h : β → ι → ℝ) :
    ∑ j, w j * (∑ x ∈ O, u x * f x j) * (∑ y ∈ N, v y * h y j)
      = ∑ x ∈ O, ∑ y ∈ N, (u x * v y) * ∑ j, w j * f x j * h y j := by
  have h1 : ∀ j, w j * (∑ x ∈ O, u x * f x j) * (∑ y ∈ N, v y * h y j)
      = ∑ x ∈ O, ∑ y ∈ N, (u x * v y) * (w j * f x j * h y j) := by
    intro j
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact (Finset.mul_sum _ _ _).symm
end AaronsonAmbainis
