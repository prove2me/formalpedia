-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:05:22.679199+00:00
-- url     : https://prove2.me/submissions/9cf4263e-db11-4549-b7dc-f7cdd29faa2e

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_add

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {α : Type*} (s : Finset α) {F : α → Cube ι → ℝ} {d : ℕ}
    (h : ∀ k ∈ s, HasDegreeLE (F k) d) : HasDegreeLE (fun x => ∑ k ∈ s, F k x) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDegreeLE_const (ι := ι) 0 d
  | insert k s hk ih =>
    have h1 : HasDegreeLE (fun x => F k x + ∑ k ∈ s, F k x) d :=
      hasDegreeLE_add (h k (Finset.mem_insert_self k s))
        (ih (fun k' hk' => h k' (Finset.mem_insert_of_mem hk')))
    have h2 : (fun x => ∑ k ∈ insert k s, F k x) = fun x => F k x + ∑ k ∈ s, F k x := by
      funext x
      rw [Finset.sum_insert hk]
    rw [h2]
    exact h1
end AaronsonAmbainis.Bridge
