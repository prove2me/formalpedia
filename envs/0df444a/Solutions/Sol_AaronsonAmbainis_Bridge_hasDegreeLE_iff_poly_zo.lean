-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_iff_poly_zo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:51:32.824547+00:00
-- url     : https://prove2.me/submissions/eafc889e-6c82-4a38-9510-5a5c274be804

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval_zo
import Theorems.Thm_AaronsonAmbainis_Bridge_exists_poly_of_hasDegreeLE

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (zoPt x) p := by
  constructor
  · exact exists_poly_of_hasDegreeLE (a := 1) (b := -2)
      (fun x i => by unfold zoPt; split_ifs <;> norm_num)
  · rintro ⟨p, hp, hf⟩
    have h : f = fun x => MvPolynomial.eval (zoPt x) p := funext hf
    rw [h]
    exact hasDegreeLE_eval_zo p hp
end AaronsonAmbainis.Bridge
