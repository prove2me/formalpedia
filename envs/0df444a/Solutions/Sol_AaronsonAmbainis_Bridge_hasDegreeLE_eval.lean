-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:47:33.163705+00:00
-- url     : https://prove2.me/submissions/2f0c9c33-3277-4bf5-92bd-1b0aa8af3ec3

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_mono
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_pow
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_prod
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_smul
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_sum


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {v : Cube ι → ι → ℝ} (hv : ∀ i, HasDegreeLE (fun x => v x i) 1)
    (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x => MvPolynomial.eval (v x) p) d := by
  have h1 : (fun x => MvPolynomial.eval (v x) p)
      = fun x => ∑ m ∈ p.support, p.coeff m * ∏ i, v x i ^ m i := by
    funext x
    exact MvPolynomial.eval_eq' (v x) p
  rw [h1]
  refine hasDegreeLE_sum _ (fun m hm => hasDegreeLE_smul _ ?_)
  have h2 : ∑ i, m i ≤ d := by
    have h3 := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h3
    exact h3.trans hp
  refine hasDegreeLE_mono ?_ h2
  have h4 : HasDegreeLE (fun x => ∏ i, v x i ^ m i) (∑ i, m i * 1) :=
    hasDegreeLE_prod (univ : Finset ι) (F := fun i x => v x i ^ m i) (k := fun i => m i * 1)
      (fun i _ => hasDegreeLE_pow (hv i) (m i))
  simpa only [mul_one] using h4
end AaronsonAmbainis.Bridge
