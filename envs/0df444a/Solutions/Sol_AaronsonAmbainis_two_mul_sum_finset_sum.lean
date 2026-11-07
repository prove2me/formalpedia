-- Prove2me | solution 1 for AaronsonAmbainis.two_mul_sum_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:52.161599+00:00
-- url     : https://prove2.me/submissions/a1cc1c49-8be4-4933-894b-a5f78846aabd

import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairs

set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (β : ι → ℝ) :
    2 * ∑ F : Finset ι, ∑ j ∈ F, β j = 2 ^ Fintype.card ι * ∑ j, β j := by
  have hcompl : ∑ F : Finset ι, ∑ j ∈ Fᶜ, β j = ∑ F : Finset ι, ∑ j ∈ F, β j :=
    Fintype.sum_bijective (compl : Finset ι → Finset ι) compl_bijective
      (fun F => ∑ j ∈ Fᶜ, β j) (fun F => ∑ j ∈ F, β j) (fun _ => rfl)
  calc 2 * ∑ F : Finset ι, ∑ j ∈ F, β j
      = ∑ F : Finset ι, ∑ j ∈ F, β j + ∑ F : Finset ι, ∑ j ∈ Fᶜ, β j := by
        rw [hcompl]; ring
    _ = ∑ F : Finset ι, (∑ j ∈ F, β j + ∑ j ∈ Fᶜ, β j) := Finset.sum_add_distrib.symm
    _ = ∑ _F : Finset ι, ∑ j, β j := by
        apply Finset.sum_congr rfl
        intro F _
        exact Finset.sum_add_sum_compl F β
    _ = 2 ^ Fintype.card ι * ∑ j, β j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]
        push_cast
        ring
end AaronsonAmbainis
