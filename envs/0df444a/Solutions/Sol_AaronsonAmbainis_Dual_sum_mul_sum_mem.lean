-- Prove2me | solution 1 for AaronsonAmbainis.Dual.sum_mul_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:44:52.878275+00:00
-- url     : https://prove2.me/submissions/47831675-ae83-4731-b7f6-c83b03454104

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Core

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (κ : Finset ι → ℝ) (a : ι → ℝ) :
    ∑ S, κ S * ∑ i ∈ S, a i
      = ∑ i, a i * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := by
  have h1 : ∀ S : Finset ι, κ S * ∑ i ∈ S, a i = ∑ i, if i ∈ S then a i * κ S else 0 := by
    intro S
    rw [Fintype.sum_ite_mem, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : ∀ i : ι, a i * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S
      = ∑ S : Finset ι, if i ∈ S then a i * κ S else 0 := by
    intro i
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun S _ => h1 S, Finset.sum_congr rfl fun i _ => h2 i]
  exact Finset.sum_comm
end AaronsonAmbainis.Dual
