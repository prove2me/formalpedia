-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.totalDegree_letter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:40.354194+00:00
-- url     : https://prove2.me/submissions/1f98b377-8283-429f-b89e-7f3ce9085373

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (a b : ℝ) (i : ι) :
    (C a + C b * X i : MvPolynomial ι ℝ).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]
    exact Nat.zero_le 1
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]
end AaronsonAmbainis.Bridge
