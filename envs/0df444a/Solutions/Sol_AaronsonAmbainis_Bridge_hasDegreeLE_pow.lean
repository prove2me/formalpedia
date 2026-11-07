-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:44:59.005434+00:00
-- url     : https://prove2.me/submissions/35aac58d-9183-4efb-a42a-5d1f7b872c60

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_mul

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {g : Cube ι → ℝ} {k : ℕ} (hg : HasDegreeLE g k) (m : ℕ) :
    HasDegreeLE (fun x => g x ^ m) (m * k) := by
  induction m with
  | zero => simpa using hasDegreeLE_const (ι := ι) 1 0
  | succ m ih =>
    have h2 : (fun x => g x ^ (m + 1)) = fun x => g x ^ m * g x := by
      funext x
      rw [pow_succ]
    rw [h2, add_one_mul]
    exact hasDegreeLE_mul ih hg
end AaronsonAmbainis.Bridge
