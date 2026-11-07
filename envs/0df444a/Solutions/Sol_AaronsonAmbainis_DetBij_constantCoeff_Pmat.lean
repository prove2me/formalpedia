-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.constantCoeff_Pmat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:19.408863+00:00
-- url     : https://prove2.me/submissions/9f02aa68-8f97-4b23-88e9-99b1baa471d1

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Theorems.Thm_AaronsonAmbainis_DetBij_Pmat_apply
import Theorems.Thm_AaronsonAmbainis_DetBij_diffSet_eq_empty_iff


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x w : Ones g) :
    constantCoeff (Pmat g A x w) = if x = w then 1 else 0 := by
  by_cases hxw : x = w
  · subst hxw
    rw [if_pos rfl, Pmat_apply, diffSet_eq_empty_iff.mpr rfl, if_pos (Finset.empty_subset _),
      Finset.prod_empty, map_one]
  · rw [if_neg hxw, Pmat_apply]
    split_ifs with h
    · have hne : (diffSet x.1 w.1).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        exact fun h0 => hxw (Subtype.ext (diffSet_eq_empty_iff.mp h0))
      obtain ⟨i, hi⟩ := hne
      rw [map_prod]
      exact Finset.prod_eq_zero hi (by simp)
    · exact map_zero _
end AaronsonAmbainis.DetBij
