-- Prove2me | solution 1 for AaronsonAmbainis.sum_ite_ite_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:28.464957+00:00
-- url     : https://prove2.me/submissions/425272cd-fcf6-4e40-a681-39c30ab490ef

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (F : Finset ι) (w a b : ι → ℝ) :
    ∑ j, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0)
      = ∑ j ∈ F, w j * a j * b j := by
  have h1 : ∑ j ∈ F, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0)
      = ∑ j, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0) := by
    apply Finset.sum_subset (Finset.subset_univ F)
    intro j _ hj
    simp [hj]
  rw [← h1]
  apply Finset.sum_congr rfl
  intro j hj
  simp [hj]
end AaronsonAmbainis
