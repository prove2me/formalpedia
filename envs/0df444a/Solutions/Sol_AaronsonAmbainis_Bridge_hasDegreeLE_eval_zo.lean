-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_eval_zo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:49:43.906411+00:00
-- url     : https://prove2.me/submissions/251a5ff5-46ef-4b85-8bdf-0deea4f42e4b

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_zo_coord


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x : Cube ι => MvPolynomial.eval (zoPt x) p) d :=
  hasDegreeLE_eval (v := zoPt) hasDegreeLE_zo_coord p hp
end AaronsonAmbainis.Bridge
