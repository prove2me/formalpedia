-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.agMon_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:14.658198+00:00
-- url     : https://prove2.me/submissions/7df6fe5a-0540-4708-99ca-eb96aa297aee

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x z : Cube ι) :
    agMon x z = monomial (agExp x z) (1 : ℤ) := by
  rw [agExp, monomial_sum_one]
  unfold agMon
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · simp
end AaronsonAmbainis.DetBij
