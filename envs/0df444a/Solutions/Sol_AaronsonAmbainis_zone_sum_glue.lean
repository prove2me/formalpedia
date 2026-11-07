-- Prove2me | solution 1 for AaronsonAmbainis.zone_sum_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:35:59.033541+00:00
-- url     : https://prove2.me/submissions/7208cb32-957f-476f-9628-0d01dd9ee14a

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Theorems.Thm_AaronsonAmbainis_sum_ite_ite_mem
import Theorems.Thm_AaronsonAmbainis_glue_antipode


set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis
theorem _root_.solution (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ)
    (F : Finset ι) (z : Cube ι) :
    ∑ u ∈ zone (fun u => g (glue F z u)),
        (∑ j, w j * (if j ∈ F then lam (glue F z u) j else 0)
          * (if j ∈ F then lam (glue F z (antipode u)) j else 0))⁻¹
      = ∑ u, allPairsTerm g w lam F (glue F z u) := by
  unfold zone
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  simp only [glue_antipode, sum_ite_ite_mem, allPairsTerm]
end AaronsonAmbainis
