-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.exists_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:01.633196+00:00
-- url     : https://prove2.me/submissions/6ba86038-3aa4-4c80-9e93-c4b464ba6429

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Theorems.Thm_AaronsonAmbainis_DetBij_exists_lowest_Qmat
import Theorems.Thm_AaronsonAmbainis_DetBij_exists_perm_of_mem_support
import Theorems.Thm_AaronsonAmbainis_DetBij_sum_agExp_apply

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ σ : Equiv.Perm (Ones g), (∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)) ∧
      ∀ j, (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card ≤ bdry g j := by
  obtain ⟨m, hm, hmb⟩ := exists_lowest_Qmat hU hB g A hA
  obtain ⟨σ, hσ, rfl⟩ := exists_perm_of_mem_support g A m hm
  refine ⟨σ, hσ, fun j => ?_⟩
  rw [← sum_agExp_apply]
  exact hmb j
end AaronsonAmbainis.DetBij
