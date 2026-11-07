-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.Qmat_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:41.917765+00:00
-- url     : https://prove2.me/submissions/503c1089-0fd2-4bfd-af9f-f49e3c761213

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Theorems.Thm_AaronsonAmbainis_DetBij_Qmat_apply
import Theorems.Thm_AaronsonAmbainis_DetBij_agMon_eq_monomial


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι) (σ : Equiv.Perm (Ones g)) :
    ∏ x : Ones g, Qmat g A (σ x) x
      = if ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)
        then monomial (∑ x : Ones g, agExp (σ x).1 x.1) (1 : ℤ) else 0 := by
  split_ifs with h
  · rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Qmat_apply, if_pos (h x), agMon_eq_monomial]
  · have h' : ∃ x : Ones g, ¬ Disjoint (agSet (σ x).1 x.1) (A (σ x).1) := not_forall.mp h
    obtain ⟨x, hx⟩ := h'
    refine Finset.prod_eq_zero (Finset.mem_univ x) ?_
    rw [Qmat_apply, if_neg hx]
end AaronsonAmbainis.DetBij
