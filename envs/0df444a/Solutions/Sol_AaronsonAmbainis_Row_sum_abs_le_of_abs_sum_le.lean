-- Prove2me | solution 1 for AaronsonAmbainis.Row.sum_abs_le_of_abs_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:09:21.406671+00:00
-- url     : https://prove2.me/submissions/a3dfe893-5a17-4196-bb97-e83ef57213b6

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
namespace AaronsonAmbainis.Row
theorem _root_.solution {β : Type*} [Fintype β] (d : β → ℝ) (K : ℝ)
    (h : ∀ R : Finset β, |∑ b ∈ R, d b| ≤ K) : ∑ b, |d b| ≤ 2 * K := by
  have hA : ∑ b ∈ univ.filter (fun b => 0 ≤ d b), |d b|
      = ∑ b ∈ univ.filter (fun b => 0 ≤ d b), d b :=
    Finset.sum_congr rfl (fun b hb => abs_of_nonneg (Finset.mem_filter.mp hb).2)
  have hB : ∑ b ∈ univ.filter (fun b => ¬ 0 ≤ d b), |d b|
      = -∑ b ∈ univ.filter (fun b => ¬ 0 ≤ d b), d b := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun b hb => abs_of_neg (not_le.mp (Finset.mem_filter.mp hb).2))
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun b => 0 ≤ d b) (fun b => |d b|)
  have h1 := (abs_le.mp (h (univ.filter (fun b => 0 ≤ d b)))).2
  have h2 := (abs_le.mp (h (univ.filter (fun b => ¬ 0 ≤ d b)))).1
  linarith
end AaronsonAmbainis.Row
