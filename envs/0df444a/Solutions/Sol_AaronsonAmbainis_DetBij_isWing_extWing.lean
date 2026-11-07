-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.isWing_extWing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:34:40.9482+00:00
-- url     : https://prove2.me/submissions/279917f8-0fb7-4695-a726-681f5be47d11

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main
import Theorems.Thm_AaronsonAmbainis_DetBij_extWing_of_mem
import Theorems.Thm_AaronsonAmbainis_DetBij_extWing_of_notMem
import Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_empty


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ u ∈ zone g, IsWing g u (A u)) (x : Ones g) :
    IsWing g x.1 (extWing g A x.1) := by
  by_cases hx : x.1 ∈ zone g
  · rw [extWing_of_mem g A hx]
    exact hA x.1 hx
  · intro S hS
    rw [extWing_of_notMem g A hx] at hS
    rw [Finset.subset_empty.mp hS, flipSet_empty]
    exact x.2
end AaronsonAmbainis.DetBij
