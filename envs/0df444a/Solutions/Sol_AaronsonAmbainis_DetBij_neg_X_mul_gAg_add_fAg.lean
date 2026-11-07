-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.neg_X_mul_gAg_add_fAg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:18.783566+00:00
-- url     : https://prove2.me/submissions/888371d2-aba2-480e-8c43-b0056cbbd096

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x z : Cube ι) (i : ι) :
    -(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i
      = if x i = z i then 0 else 1 - (X i : MvPolynomial ι ℤ) ^ 2 := by
  unfold fAg gAg
  split_ifs <;> ring
end AaronsonAmbainis.DetBij
