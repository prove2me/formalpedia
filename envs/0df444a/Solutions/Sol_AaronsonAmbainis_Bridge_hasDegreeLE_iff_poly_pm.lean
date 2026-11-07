-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_iff_poly_pm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:51:35.52445+00:00
-- url     : https://prove2.me/submissions/5625f96e-f5a5-4727-a1bc-71563b557337

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval_pm
import Theorems.Thm_AaronsonAmbainis_Bridge_exists_poly_of_hasDegreeLE

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (pmPt x) p := by
  constructor
  · exact exists_poly_of_hasDegreeLE (a := 0) (b := 1)
      (fun x i => by unfold pmPt; split_ifs <;> norm_num)
  · rintro ⟨p, hp, hf⟩
    have h : f = fun x => MvPolynomial.eval (pmPt x) p := funext hf
    rw [h]
    exact hasDegreeLE_eval_pm p hp
end AaronsonAmbainis.Bridge
