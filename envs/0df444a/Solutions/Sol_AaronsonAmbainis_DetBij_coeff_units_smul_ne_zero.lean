-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.coeff_units_smul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:28.817813+00:00
-- url     : https://prove2.me/submissions/16af7ffc-7648-459b-a8ac-9d792076c273

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (m : ι →₀ ℕ) (u : ℤˣ) (p : MvPolynomial ι ℤ)
    (h : coeff m (u • p) ≠ 0) : coeff m p ≠ 0 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using h
  · simpa using h
end AaronsonAmbainis.DetBij
