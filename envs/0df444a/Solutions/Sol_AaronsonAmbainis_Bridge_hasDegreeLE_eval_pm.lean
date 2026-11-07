-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_eval_pm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:49:44.715247+00:00
-- url     : https://prove2.me/submissions/100207a6-3cb8-44a4-9c25-b9570aa4a7f3

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_pm_coord


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x : Cube ι => MvPolynomial.eval (pmPt x) p) d :=
  hasDegreeLE_eval (v := pmPt) hasDegreeLE_pm_coord p hp
end AaronsonAmbainis.Bridge
